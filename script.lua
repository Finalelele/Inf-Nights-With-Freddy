local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 30) then
					if (Enum <= 14) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								elseif (Enum > 1) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 5) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 10) then
							if (Enum <= 8) then
								if (Enum > 7) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum == 9) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 12) then
							if (Enum > 11) then
								Stk[Inst[2]]();
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 13) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 22) then
						if (Enum <= 18) then
							if (Enum <= 16) then
								if (Enum > 15) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum > 17) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 20) then
							if (Enum > 19) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum == 21) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							do
								return;
							end
						end
					elseif (Enum <= 26) then
						if (Enum <= 24) then
							if (Enum > 23) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 25) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 28) then
						if (Enum == 27) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum > 29) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 46) then
					if (Enum <= 38) then
						if (Enum <= 34) then
							if (Enum <= 32) then
								if (Enum == 31) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								else
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 44) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum == 33) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 36) then
							if (Enum == 35) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum > 37) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 42) then
						if (Enum <= 40) then
							if (Enum == 39) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum == 41) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							do
								return;
							end
						end
					elseif (Enum <= 44) then
						if (Enum > 43) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 44) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum == 45) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A]();
					end
				elseif (Enum <= 54) then
					if (Enum <= 50) then
						if (Enum <= 48) then
							if (Enum == 47) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 49) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 52) then
						if (Enum > 51) then
							Stk[Inst[2]] = {};
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 53) then
						VIP = Inst[3];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 58) then
					if (Enum <= 56) then
						if (Enum > 55) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum > 57) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					end
				elseif (Enum <= 60) then
					if (Enum > 59) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum > 61) then
					Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
				else
					Upvalues[Inst[3]] = Stk[Inst[2]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!233Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403183Q00682Q7470733A2Q2F7369726975732E6D656E752F67656E32030C3Q0043726561746557696E646F7703043Q006E616D6503163Q00496E66204E69676874732057697468204672652Q647903083Q007375627469746C65030D3Q0062792046696E616C656C656C6503053Q007468656D6503063Q00636F62616C74030D3Q00636F6E66696775726174696F6E03083Q006175746F536176652Q0103083Q006175746F4C6F616403083Q0066696C654E616D6503063Q00436F6E666967030C3Q00637573746F6D466F6C646572031A3Q00537572766976655468654B692Q6C657246696E616C656C656C6503093Q0043726561746554616203043Q004D697363030C3Q0043726561746542752Q746F6E03083Q00476F64204D6F646503083Q0063612Q6C6261636B030C3Q00437265617465546F2Q676C65030F3Q00496E7374616E74496E74657261637403043Q00666C616703053Q0076616C7565010003193Q004175746F2057696E2047616D626C696E67204D616368696E6503163Q006175746F57696E47616D626C696E674D616368696E6503093Q0045737020547261736803083Q00657370547261736803053Q004F7468657203233Q00556E6976657273616C205363726970742028666F722065737020616E64206D6F72652900493Q0012303Q00013Q001230000100023Q002038000100010003001233000300044Q000B000100034Q00295Q00022Q002E3Q0001000200203800013Q00052Q003400033Q000400301E00030006000700301E00030008000900301E0003000A000B2Q003400043Q000400301E0004000D000E00301E0004000F000E00301E00040010001100301E00040012001300100D0003000C00042Q00020001000300022Q0039000200024Q003400036Q0039000400073Q0020380008000100142Q0034000A3Q000100301E000A000600152Q00020008000A00020020380009000800162Q0034000B3Q000200301E000B00060017000620000C3Q000100012Q002C3Q00063Q00100D000B0018000C2Q00120009000B00010020380009000800192Q0034000B3Q000400301E000B0006001A00301E000B001B001A00301E000B001C001D000620000C0001000100032Q002C3Q00034Q002C3Q00044Q002C3Q00053Q00100D000B0018000C2Q00120009000B00010020380009000800192Q0034000B3Q000400301E000B0006001E00301E000B001B001F00301E000B001C001D000620000C0002000100012Q002C3Q00023Q00100D000B0018000C2Q00120009000B00010020380009000800192Q0034000B3Q000400301E000B0006002000301E000B001B002100301E000B001C001D000620000C0003000100012Q002C3Q00073Q00100D000B0018000C2Q00120009000B00010020380009000100142Q0034000B3Q000100301E000B000600222Q00020009000B0002002038000A000900162Q0034000C3Q000200301E000C00060023000206000D00043Q00100D000C0018000D2Q0012000A000C00012Q00163Q00013Q00053Q000A3Q00030A3Q00446973636F2Q6E65637403063Q0069706169727303093Q00776F726B7370616365030C3Q00416E696D6174726F6E696373030B3Q004765744368696C6472656E030E3Q0046696E6446697273744368696C64030B3Q00412Q7461636B4576656E7403073Q0044657374726F79030A3Q004368696C64412Q64656403073Q00436F2Q6E65637400214Q00357Q0006223Q000800013Q0004363Q000800012Q00357Q0020385Q00012Q00183Q000200012Q00398Q001B7Q0012303Q00023Q001230000100033Q0020100001000100040020380001000100052Q0005000100024Q00275Q00020004363Q00170001002038000500040006001233000700074Q00020005000700020006220005001700013Q0004363Q001700010020100005000400070020380005000500082Q00180005000200010006323Q000F000100020004363Q000F00010012303Q00033Q0020105Q00040020105Q00090020385Q000A00020600026Q00023Q000200022Q001B8Q00163Q00013Q00013Q00063Q0003043Q007461736B03043Q0077616974026Q00E03F030E3Q0046696E6446697273744368696C64030B3Q00412Q7461636B4576656E7403073Q0044657374726F79010D3Q001230000100013Q002010000100010002001233000200034Q001800010002000100203800013Q0004001233000300054Q00020001000300020006220001000C00013Q0004363Q000C000100201000013Q00050020380001000100062Q00180001000200012Q00163Q00017Q000C3Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q00497341030F3Q0050726F78696D69747950726F6D7074030C3Q00486F6C644475726174696F6E028Q00030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403123Q0044657363656E64616E7452656D6F76696E6700030A3Q00446973636F2Q6E656374014D3Q0006223Q002600013Q0004363Q00260001001230000100013Q001230000200023Q0020380002000200032Q0005000200034Q002700013Q00030004363Q00150001002038000600050004001233000800054Q00020006000800020006220006001500013Q0004363Q001500012Q003500066Q003E00060006000500060100060014000100010004363Q001400012Q003500065Q0020100007000500062Q000A00060005000700301E00050006000700063200010008000100020004363Q00080001001230000100023Q00201000010001000800203800010001000900062000033Q000100012Q00258Q00020001000300022Q001B000100013Q001230000100023Q00201000010001000A00203800010001000900062000030001000100012Q00258Q00020001000300022Q001B000100023Q0004363Q004C0001001230000100013Q001230000200023Q0020380002000200032Q0005000200034Q002700013Q00030004363Q003A0001002038000600050004001233000800054Q00020006000800020006220006003A00013Q0004363Q003A00012Q003500066Q003E0006000600050006220006003A00013Q0004363Q003A00012Q003500066Q003E00060006000500100D0005000600062Q003500065Q00202Q00060005000B0006320001002C000100020004363Q002C00012Q0035000100013Q0006220001004400013Q0004363Q004400012Q0035000100013Q00203800010001000C2Q00180001000200012Q0039000100014Q001B000100014Q0035000100023Q0006220001004C00013Q0004363Q004C00012Q0035000100023Q00203800010001000C2Q00180001000200012Q0039000100014Q001B000100024Q00163Q00013Q00023Q00043Q002Q033Q00497341030F3Q0050726F78696D69747950726F6D7074030C3Q00486F6C644475726174696F6E028Q00010E3Q00203800013Q0001001233000300024Q00020001000300020006220001000D00013Q0004363Q000D00012Q003500016Q003E000100013Q0006010001000D000100010004363Q000D00012Q003500015Q00201000023Q00032Q000A00013Q000200301E3Q000300042Q00163Q00017Q00033Q002Q033Q00497341030F3Q0050726F78696D69747950726F6D70740001083Q00203800013Q0001001233000300024Q00020001000300020006220001000700013Q0004363Q000700012Q003500015Q00202Q00013Q00032Q00163Q00017Q00073Q0003093Q00776F726B737061636503043Q0053686F70030A3Q0046756E4D616368696E6503053Q0042612Q6C73030A3Q004368696C64412Q64656403073Q00436F2Q6E656374030A3Q00446973636F2Q6E65637401153Q0006223Q000C00013Q0004363Q000C0001001230000100013Q00201000010001000200201000010001000300201000010001000400201000010001000500203800010001000600020600036Q00020001000300022Q001B00015Q0004363Q001400012Q003500015Q0006220001001400013Q0004363Q001400012Q003500015Q0020380001000100072Q00180001000200012Q0039000100014Q001B00016Q00163Q00013Q00013Q00063Q0003063Q00434672616D6503093Q00776F726B737061636503043Q0053686F70030A3Q0046756E4D616368696E6503053Q005A6F6E657303043Q00472Q4F4401083Q001230000100023Q00201000010001000300201000010001000400201000010001000500201000010001000600201000010001000100100D3Q000100012Q00163Q00017Q00163Q0003063Q0069706169727303093Q00776F726B73706163652Q033Q004D617003053Q005472617368030C3Q0043752Q72656E745472617368030B3Q004765744368696C6472656E030E3Q0046696E6446697273744368696C6403083Q00657370545261736803083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742028Q00025Q00E06F4003043Q004E616D65030A3Q004368696C64412Q64656403073Q00436F2Q6E656374030A3Q00446973636F2Q6E65637403073Q0044657374726F7901453Q0006223Q002900013Q0004363Q00290001001230000100013Q001230000200023Q0020100002000200030020100002000200040020100002000200050020380002000200062Q0005000200034Q002700013Q00030004363Q001D0001002038000600050007001233000800084Q00020006000800020006010006001D000100010004363Q001D0001001230000600093Q00201000060006000A0012330007000B4Q000400060002000200100D0006000C00050012300007000E3Q00201000070007000F001233000800103Q001233000900103Q001233000A00114Q00020007000A000200100D0006000D000700301E0006001200080006320001000B000100020004363Q000B0001001230000100023Q00201000010001000300201000010001000400201000010001000500201000010001001300203800010001001400020600036Q00020001000300022Q001B00015Q0004363Q004400012Q003500015Q0006220001003100013Q0004363Q003100012Q003500015Q0020380001000100152Q00180001000200012Q0039000100014Q001B00015Q001230000100013Q001230000200023Q0020100002000200030020100002000200040020100002000200050020380002000200062Q0005000200034Q002700013Q00030004363Q00420001002038000600050007001233000800084Q00020006000800020006220006004200013Q0004363Q004200010020100006000500080020380006000600162Q00180006000200010006320001003A000100020004363Q003A00012Q00163Q00013Q00013Q000C3Q00030E3Q0046696E6446697273744368696C6403083Q00657370545261736803083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742028Q00025Q00E06F4003043Q004E616D6501133Q00203800013Q0001001233000300024Q000200010003000200060100010012000100010004363Q00120001001230000100033Q002010000100010004001233000200054Q000400010002000200100D000100063Q001230000200083Q0020100002000200090012330003000A3Q0012330004000A3Q0012330005000B4Q000200020005000200100D00010007000200301E0001000C00022Q00163Q00017Q00053Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574035A3Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F46696E616C656C656C652F556E6976657273616C5363726970742F726566732F68656164732F6D61696E2F7363726970742E6C75613F743D03043Q007469636B000B3Q0012303Q00013Q001230000100023Q002038000100010003001233000300043Q001230000400054Q002E0004000100022Q00240003000300042Q000B000100034Q00295Q00022Q000C3Q000100012Q00163Q00017Q00", GetFEnv(), ...);
