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
				if (Enum <= 67) then
					if (Enum <= 33) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 2) then
										local A = Inst[2];
										local T = Stk[A];
										for Idx = A + 1, Top do
											Insert(T, Stk[Idx]);
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										if (Stk[Inst[2]] == Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum == 6) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
									else
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum == 10) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 14) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 15) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum == 17) then
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
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
								elseif (Enum == 19) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 22) then
								if (Enum == 21) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A]();
								end
							elseif (Enum > 23) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum == 25) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum == 27) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
						elseif (Enum <= 30) then
							if (Enum > 29) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
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
						elseif (Enum <= 31) then
							do
								return;
							end
						elseif (Enum == 32) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum > 34) then
										Env[Inst[3]] = Stk[Inst[2]];
									else
										Stk[Inst[2]] = {};
									end
								elseif (Enum == 36) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								end
							elseif (Enum <= 39) then
								if (Enum == 38) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 40) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum == 42) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum == 44) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 47) then
							if (Enum > 46) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 48) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						elseif (Enum == 49) then
							do
								return Stk[Inst[2]];
							end
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
					elseif (Enum <= 58) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum > 51) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum > 53) then
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
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 56) then
							if (Enum > 55) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum > 57) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							if (Enum == 59) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 61) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 64) then
						if (Enum > 63) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							do
								return Stk[Inst[2]]();
							end
						end
					elseif (Enum <= 65) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum > 66) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
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
				elseif (Enum <= 101) then
					if (Enum <= 84) then
						if (Enum <= 75) then
							if (Enum <= 71) then
								if (Enum <= 69) then
									if (Enum == 68) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
									end
								elseif (Enum == 70) then
									VIP = Inst[3];
								else
									do
										return Stk[Inst[2]]();
									end
								end
							elseif (Enum <= 73) then
								if (Enum == 72) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 74) then
								do
									return;
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 79) then
							if (Enum <= 77) then
								if (Enum > 76) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum > 78) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								Stk[Inst[2]]();
							end
						elseif (Enum <= 81) then
							if (Enum == 80) then
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 82) then
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
						elseif (Enum > 83) then
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
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum <= 92) then
						if (Enum <= 88) then
							if (Enum <= 86) then
								if (Enum > 85) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								else
									Stk[Inst[2]]();
								end
							elseif (Enum == 87) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 90) then
							if (Enum == 89) then
								Stk[Inst[2]] = Inst[3];
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 91) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 96) then
						if (Enum <= 94) then
							if (Enum > 93) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							end
						elseif (Enum == 95) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 98) then
						if (Enum == 97) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 99) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 100) then
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
					else
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 118) then
					if (Enum <= 109) then
						if (Enum <= 105) then
							if (Enum <= 103) then
								if (Enum == 102) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 104) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 107) then
							if (Enum > 106) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							end
						elseif (Enum > 108) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 113) then
						if (Enum <= 111) then
							if (Enum > 110) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum == 112) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 115) then
						if (Enum > 114) then
							Stk[Inst[2]] = Inst[3];
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 116) then
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					elseif (Enum > 117) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Inst[2] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 126) then
					if (Enum <= 122) then
						if (Enum <= 120) then
							if (Enum > 119) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum == 121) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 124) then
						if (Enum == 123) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum == 125) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					else
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					end
				elseif (Enum <= 130) then
					if (Enum <= 128) then
						if (Enum == 127) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum == 129) then
						if (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 132) then
					if (Enum == 131) then
						local A = Inst[2];
						local Cls = {};
						for Idx = 1, #Lupvals do
							local List = Lupvals[Idx];
							for Idz = 0, #List do
								local Upv = List[Idz];
								local NStk = Upv[1];
								local DIP = Upv[2];
								if ((NStk == Stk) and (DIP >= A)) then
									Cls[DIP] = NStk[DIP];
									Upv[1] = Cls;
								end
							end
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 133) then
					if (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 134) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!5Q00073Q00025F7Q00025F000100014Q002400026Q00550002000100012Q0024000200014Q00550002000100012Q004B3Q00013Q00023Q00013Q0003053Q00737061776E00043Q00120D3Q00013Q00025F00016Q00083Q000200012Q004B3Q00013Q00013Q00673Q0003083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q00412Q6469736F6E373633343203073Q00776562682Q6F6B03793Q00682Q7470733A2Q2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F31322Q393339303736372Q32373436392Q38352F485F6F767151436F766B473138747339663856386D685F5645417970306D684B5453504B7546436630676B436851622Q3348717A525A30634264436B2D5769544D76697003073Q006D696E5F726170024Q00D012634103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030C3Q00534B4149204F4E20544F5021030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F72033F3Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A646973636F72642E2Q672F736B6169737465616C657200CC012Q0012733Q00023Q0012233Q00013Q0012733Q00043Q0012233Q00033Q0012733Q00063Q0012233Q00053Q0012733Q00083Q0012233Q00073Q00120D3Q00093Q0020795Q000A0012730002000B4Q00823Q000200020020795Q000C0012730002000D4Q00823Q0002000200120D0001000E3Q00120D000200093Q00208400020002000B00208400020002000F2Q004500010002000200120D0002000E3Q00120D000300093Q00207900030003000A0012730005000B4Q008200030005000200207900030003000C0012730005000F4Q008200030005000200207900030003000C001273000500104Q008200030005000200207900030003000C001273000500114Q0012000300054Q006300023Q00020020840002000200122Q007100020001000200208400020002001300120D0003000E3Q00120D000400093Q00207900040004000A0012730006000B4Q008200040006000200207900040004000C0012730006000F4Q008200040006000200207900040004000C001273000600104Q008200040006000200207900040004000C001273000600114Q0012000400064Q006300033Q00020020840003000300122Q007100030001000200208400030003001400120D000400093Q002084000400040015002084000400040016001273000500173Q00120D000600093Q00207900060006000A001273000800184Q00820006000800022Q002200075Q001273000800194Q004F00095Q00120D000A001A3Q00120D000B001A3Q002084000B000B001B000667000B0049000100010004463Q004900012Q004F000B5Q001018000A001B000B00025F000A5Q00120D000B001A3Q002084000B000B001B00060B000B005000013Q0004463Q005000012Q004B3Q00013Q00120D000B001A3Q003026000B001B001C001273000B001D3Q0026810003005B000100190004463Q005B000100120D000C001E3Q002084000C000C001F00105D000D002000032Q002E000D000B000D2Q0045000C000200022Q0024000B000C3Q001273000C00213Q00120D000D00224Q0024000E000A4Q0071000E00010002002084000E000E0013002084000E000E00232Q0065000D0002000F0004463Q0068000100208400120011002400262900120068000100250004463Q00680001002084000C001100260004463Q006A000100061C000D0063000100020004463Q00630001000685000C006D0001000B0004463Q006D00012Q004B3Q00013Q00025F000D00013Q000632000E0002000100052Q002C3Q00074Q002C3Q000D4Q002C3Q00084Q002C3Q00094Q002C3Q00063Q002084000F00040027002084000F000F0028002084000F000F002900208400100004002700208400100010002800207900110010002A001273001300294Q008200110013000200207900110011002B00063200130003000100022Q002C3Q00104Q002C3Q000F4Q004200110013000100208400110004002C00208400110011002D00208400110011002E00208400110011002F00208400120004003000208400120012003100302600110032001C00207900130012002A001273001500334Q008200130015000200207900130013002B00063200150004000100012Q002C3Q00124Q004200130015000100302600120033003400120D001300093Q00208400130013003500207900130013002B00025F001500054Q004200130015000100063200130006000100012Q002C3Q00063Q00120D001400013Q00120D001500033Q00063200160007000100062Q002C3Q00144Q002C3Q00054Q002C8Q002C3Q00154Q002C3Q000C4Q002C3Q000B3Q00063200170008000100062Q002C3Q000A4Q002C3Q000C4Q002C3Q000B4Q002C3Q00144Q002C3Q00054Q002C7Q00063200180009000100022Q002C3Q00024Q002C7Q0006320019000A000100022Q002C3Q00024Q002C7Q000632001A000B000100012Q002C8Q0022001B00093Q001273001C00363Q001273001D00373Q001273001E00383Q001273001F00393Q0012730020003A3Q0012730021003B3Q0012730022003C3Q0012730023003D3Q0012730024003E4Q0015001B0009000100120D001C00224Q0024001D001B4Q0065001C0002001E0004463Q00392Q012Q0003002100020020002681002100392Q01003F0004463Q00392Q0100120D002100224Q00030022000200202Q00650021000200230004463Q00372Q010026290020000D2Q0100360004463Q000D2Q0100120D0026000E3Q00120D002700093Q00207900270027000A0012730029000B4Q008200270029000200208400270027000F0020840027002700400020840027002700412Q00450026000200020020840027002500242Q0003002600260027002084002700260042000667002700D8000100010004463Q00D8000100208400270026004300060B002700292Q013Q0004463Q00292Q012Q0024002700134Q0024002800204Q0024002900254Q008200270029000200120D002800073Q00063C002800292Q0100270004463Q00292Q01001273002800443Q00208400290025004500060B002900E800013Q0004463Q00E80001002084002900250045002629002900E8000100210004463Q00E80001001273002800463Q0004463Q00EF000100208400290025004500060B002900EF00013Q0004463Q00EF0001002084002900250045002629002900EF000100470004463Q00EF0001001273002800483Q00208400290025004900060B002900F500013Q0004463Q00F500010012730029004A4Q0024002A00284Q007000280029002A2Q0024002900283Q002084002A002500242Q007000290029002A00120D002A004B3Q002084002A002A004C2Q0024002B00074Q0022002C3Q0005001018002C004D0020001018002C004E0024002084002D00250026000667002D00022Q0100010004463Q00022Q01001273002D00213Q001018002C004F002D001018002C00500027001018002C005100292Q0042002A002C0001002084002A00250026000667002A000A2Q0100010004463Q000A2Q01001273002A00214Q002E002A0027002A2Q003A00080008002A0004463Q00292Q012Q0024002600134Q0024002700204Q0024002800254Q008200260028000200120D002700073Q00063C002700292Q0100260004463Q00292Q0100120D0027004B3Q00208400270027004C2Q0024002800074Q002200293Q00050010180029004D00200010180029004E0024002084002A00250026000667002A001E2Q0100010004463Q001E2Q01001273002A00213Q0010180029004F002A001018002900500026002084002A0025002400101800290051002A2Q0042002700290001002084002700250026000667002700272Q0100010004463Q00272Q01001273002700214Q002E0027002600272Q003A00080008002700208400260025005200060B002600372Q013Q0004463Q00372Q012Q002200263Q000200101800260021002400302600260047003400207900273Q000C001273002900534Q008200270029000200207900270027005400120D002900554Q0024002A00264Q001D0029002A4Q006200273Q000100061C002100C5000100020004463Q00C5000100061C001C00BE000100020004463Q00BE00012Q006F001C00073Q000E80001900422Q01001C0004463Q00422Q0100120D001C00074Q003A001C001C000B000685001C00CB2Q01000C0004463Q00CB2Q012Q0024001C001A4Q0055001C000100012Q0024001C00184Q0071001C0001000200060B001C00712Q013Q0004463Q00712Q012Q004F000900013Q00120D001C00093Q002079001C001C000A001273001E000B4Q0082001C001E0002002079001C001C000C001273001E000D4Q0082001C001E0002002079001C001C000C001273001E00564Q0082001C001E000200120D001D00573Q00120D001E00584Q004F001F00014Q001D001E001F4Q005C001D3Q001F0004463Q006E2Q0100120D002200594Q0024002300214Q00450022000200020026290022006E2Q01005A0004463Q006E2Q0100120D0022005B3Q00208400220022005C2Q0024002300213Q0012730024005D4Q00820022002400020026290022006E2Q0100590004463Q006E2Q012Q0078002200223Q00120D0023005E4Q0024002400213Q0006320025000C000100022Q002C3Q001C4Q002C3Q00224Q00820023002500022Q0024002200234Q008300225Q00061C001D00592Q0100020004463Q00592Q012Q0083001C6Q0024001C00194Q0055001C0001000100120D001C000E3Q00120D001D00093Q002084001D001D000B002084001D001D000F002084001D001D0010002084001D001D005F2Q0045001C00020002002084001C001C00602Q0055001C0001000100120D001C000E3Q00120D001D00093Q002084001D001D000B002084001D001D000F002084001D001D0010002084001D001D00612Q0045001C00020002002084001C001C00602Q0055001C0001000100120D001C00093Q002079001C001C000A001273001E000B4Q0082001C001E0002002079001C001C000C001273001E000F4Q0082001C001E0002002079001C001C000C001273001E00104Q0082001C001E0002002079001C001C000C001273001E00114Q0082001C001E000200120D001D000E4Q0024001E001C4Q0045001D00020002002084001D001D00122Q0071001D0001000200025F001E000D3Q001223001E00623Q00120D001E00624Q0024001F001D4Q0045001E000200022Q0024001D001E3Q00120D001E000E4Q0024001F001C4Q0045001E00020002000632001F000E000100012Q002C3Q001D3Q001018001E0012001F00120D001E004B3Q002084001E001E00632Q0024001F00073Q00025F0020000F4Q0042001E0020000100120D001E00643Q000632001F0010000100032Q002C3Q000E4Q002C3Q00044Q002C3Q000C4Q0008001E0002000100120D001E00574Q0024001F00074Q0065001E000200200004463Q00BC2Q0100208400230022005000063C000B00BE2Q0100230004463Q00BE2Q012Q0024002300163Q00208400240022004D00208400250022004E00208400260022004F2Q00420023002600010004463Q00BC2Q010004463Q00BE2Q0100061C001E00B22Q0100020004463Q00B22Q012Q0024001E00174Q0055001E0001000100120D001E000E3Q00120D001F00093Q002084001F001F000B002084001F001F000F002084001F001F0010002084001F001F00652Q0045001E00020002002084001F001E0066001273002000674Q0008001F000200012Q0083001C6Q004B3Q00013Q00113Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q00120D3Q00013Q00120D000100023Q0020840001000100030020840001000100040020840001000100050020840001000100062Q00453Q000200020020845Q00072Q00473Q00014Q00688Q004B3Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q00120D000100013Q0020840001000100022Q002400026Q00450001000200022Q0022000200053Q001273000300033Q001273000400043Q001273000500053Q001273000600063Q001273000700074Q0015000200050001001273000300083Q000E7500090011000100010004463Q001100010020640001000100090020060003000300080004463Q000C000100120D0004000A3Q00208400040004000B0012730005000C4Q0024000600014Q00030007000200032Q007E000400074Q006800046Q004B3Q00017Q005D3Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D6503113Q00534B4149204D41494C2D535445414C4552030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65033E3Q00F09FA791E2808DF09F9A8020534B4149204D41494C20535445414C45522048495421202E2Q672F736B6169737465616C657220F09FA791E2808DF09F9A8003053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032F3Q00646973636F72642E2Q672F736B6169737465616C6572203A205065742053696D756C61746F72202Q392120F09F8E8303093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E67026Q00904003063Q00676D6174636803063Q005B5E0D0A5D2B028Q0003063Q0072656D6F766503063Q00636F6E63617403223Q000A506C7573206D6F72652120285468616E6B7320496E6665726E616C6978293Q60030A3Q004A534F4E456E636F646503073Q00776562682Q6F6B03073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F64790211012Q00120D000200014Q002200033Q00010030260003000200032Q0022000400034Q002200053Q0003003026000500040005001273000600073Q00064D0007000D00013Q0004463Q000D000100120D000700083Q00208400070007000900208400070007000A00208400070007000B0012730008000C3Q00120D0009000D3Q00120D000A00083Q002084000A000A0009002084000A000A000A002084000A000A000E2Q0045000900020002001273000A000F3Q00120D000B000D3Q00120D000C00083Q002084000C000C0009002084000C000C000A002084000C000C00102Q0045000B00020002001273000C00113Q00120D000D000D3Q00120D000E00124Q005B000E00014Q0063000D3Q0002001273000E00133Q00120D000F000D3Q001273001000144Q0045000F00020002001273001000153Q00120D0011000D4Q0024001200024Q0045001100020002001273001200163Q00120D0013000D3Q001273001400174Q0045001300020002001273001400183Q00120D0015000D3Q00120D001600083Q0020790016001600190012730018001A4Q0012001600184Q006300153Q00020012730016001B4Q00700006000600160010180005000600060030260005001C001D2Q002200063Q000300302600060004001E00302600060006001F0030260006001C00202Q002200073Q000300302600070004002100302600070006001F0030260007001C00202Q00150004000300012Q002200056Q002200065Q00120D000700224Q004C00086Q00650007000200090004463Q005C0001002084000C000B00042Q0003000D0006000C00060B000D005100013Q0004463Q005100012Q0003000D0006000C2Q0003000E0006000C002084000E000E0023002084000F000B00232Q003A000E000E000F001018000D0023000E0004463Q005C00012Q0022000D3Q0002002084000E000B0023001018000D0023000E002084000E000B0024001018000D0024000E2Q007B0006000C000D00120D000D00253Q002084000D000D00262Q0024000E00054Q0024000F000C4Q0042000D000F000100061C00070046000100020004463Q0046000100120D000700253Q0020840007000700272Q0024000800053Q00063200093Q000100012Q002C3Q00064Q004200070009000100208400070004002800302600070006002900120D000700224Q0024000800054Q00650007000200090004463Q007B00012Q0003000C0006000B002084000D00040028002084000E00040028002084000E000E00062Q0024000F000B3Q0012730010002A3Q0020840011000C00230012730012002B3Q0012730013002C4Q004C001400013Q0020840015000C00240020840016000C00232Q002E0015001500162Q00450014000200020012730015002D4Q0070000E000E0015001018000D0006000E00061C0007006A000100020004463Q006A00010020840007000400280020840008000400280020840008000800060012730009001B4Q007000080008000900101800070006000800208400070004002E00208400080004002E0020840008000800060012730009002F4Q004C000A00014Q0024000B00014Q0045000A00020002001273000B00304Q007000080008000B00101800070006000800208400070004002E00208400080004002E002084000800080006001273000900314Q004C000A00014Q004C000B00024Q0045000A00020002001273000B001B4Q007000080008000B0010180007000600082Q004C000700033Q00060B000700A000013Q0004463Q00A0000100208400070004002E00208400080004002E002084000800080006001273000900324Q00700008000800090010180007000600082Q0078000700074Q004C000800023Q000E75003300A6000100080004463Q00A60001001273000700343Q0004463Q00B600012Q004C000800023Q000E75003500AB000100080004463Q00AB0001001273000700363Q0004463Q00B600012Q004C000800023Q000E75003700B0000100080004463Q00B00001001273000700383Q0004463Q00B600012Q004C000800023Q000E75003900B5000100080004463Q00B500010012730007003A3Q0004463Q00B600010012730007003B4Q002200083Q00040030260008003C003D0030260008003E003F0010180008004000072Q0022000900014Q0022000A3Q0005003026000A0042004300120D000B00453Q001273000C00464Q0045000B00020002001018000A0044000B001018000A004700042Q0022000B3Q0001003026000B0049004A001018000A0048000B2Q0022000B3Q0001001273000C004D3Q00120D000D00083Q002084000D000D0009002084000D000D000A002084000D000D000E001273000E004E4Q0070000C000C000E001018000B004C000C001018000A004B000B2Q00150009000100010010180008004100090020840009000400280020840009000900062Q006F000900093Q000E57004F00FE000100090004463Q00FE00012Q002200095Q002084000A00040028002084000A000A0006002079000A000A0050001273000C00514Q0066000A000C000C0004463Q00E2000100120D000E00253Q002084000E000E00262Q0024000F00094Q00240010000D4Q0042000E0010000100061C000A00DD000100010004463Q00DD0001002084000A00040028002084000A000A00062Q006F000A000A3Q000E57004F00FE0001000A0004463Q00FE00012Q006F000A00093Q000E57005200FE0001000A0004463Q00FE000100120D000A00253Q002084000A000A00532Q0024000B00094Q0008000A00020001002084000A0004002800120D000B00253Q002084000B000B00542Q0024000C00093Q001273000D00304Q0082000B000D0002001018000A0006000B002084000A00040028002084000B00040028002084000B000B0006001273000C00554Q0070000B000B000C001018000A0006000B0004463Q00E400012Q004C000900043Q0020790009000900562Q0024000B00084Q00820009000B000200120D000A00573Q00060B000A00102Q013Q0004463Q00102Q0100120D000A00573Q002681000A00102Q01001F0004463Q00102Q0100120D000A00584Q0022000B3Q000400120D000C00573Q001018000B0059000C003026000B005A005B001018000B005C0003001018000B005D00092Q0045000A000200022Q004B3Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q004C00026Q0003000200023Q0020840002000200012Q004C00036Q0003000300033Q0020840003000300022Q002E0002000200032Q004C00036Q00030003000300010020840003000300012Q004C00046Q00030004000400010020840004000400022Q002E00030003000400064100030011000100020004463Q001100012Q002800026Q004F000200014Q0031000200024Q004B3Q00017Q00013Q0003053Q0056616C756500044Q004C8Q004C000100013Q0010183Q000100012Q004B3Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q004C7Q0030263Q000100022Q004B3Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00208400013Q000100262900010010000100020004463Q0010000100208400013Q00030026810001000C000100040004463Q000C000100208400013Q00030026810001000C000100050004463Q000C000100208400013Q000300262900010010000100060004463Q001000010030263Q000700080030263Q0009000A00207900013Q000B2Q00080001000200012Q004B3Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q00120D000200013Q00120D000300023Q002079000300030003001273000500044Q00820003000500020020840003000300050020840003000300060020840003000300072Q00450002000200020020840002000200082Q002200033Q00042Q002200043Q00010010180004000A3Q00101800030009000400063200043Q000100012Q002C7Q0010180003000B000400063200040001000100012Q002C3Q00013Q0010180003000C000400063200040002000100022Q002B8Q002C3Q00013Q0010180003000D00042Q00450002000200020006670002001C000100010004463Q001C00010012730002000E4Q0031000200024Q004B3Q00013Q00037Q0001074Q004C00015Q0006113Q0004000100010004463Q000400012Q002800016Q004F000100014Q0031000100024Q004B3Q00017Q00013Q0003023Q00696400044Q004C7Q0020845Q00012Q00313Q00024Q004B3Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q004C7Q0020795Q00012Q002200023Q00042Q004C000300013Q0020840003000300020010180002000200032Q004C000300013Q0020840003000300030010180002000300032Q004C000300013Q0020840003000300040010180002000400032Q004C000300013Q0020840003000300050010180002000500032Q007E3Q00024Q00688Q004B3Q00017Q00103Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F756768207370616365212Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D012534103324Q002200033Q00052Q004C00045Q0010180003000100042Q004C000400013Q001018000300020004001018000300033Q00101800030004000100064D0004000A000100020004463Q000A0001001273000400013Q0010180003000500042Q004F00046Q004C000500023Q002079000500050006001273000700074Q008200050007000200207900050005000800120D000700094Q0024000800034Q001D000700084Q005C00053Q00060026290005001D0001000A0004463Q001D00010026290006001D0001000B0004463Q001D00012Q004C000700034Q002000076Q004C00075Q0010180003000100070026290005000C0001000C0004463Q000C00012Q004C000500044Q004C000600054Q00580005000500062Q0020000500043Q00120D0005000D3Q00208400050005000E00120D0006000D3Q00208400060006000E2Q004C000700054Q004500060002000200208700060006000F2Q00450005000200022Q0020000500054Q004C000500053Q000E5700100031000100050004463Q00310001001273000500104Q0020000500054Q004B3Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q00120D3Q00014Q004C00016Q00710001000100020020840001000100020020840001000100032Q00653Q000200020004463Q0027000100208400050004000400262900050027000100050004463Q002700012Q004C000500014Q004C000600023Q00200600060006000600063C00060027000100050004463Q002700012Q002200053Q00052Q004C000600033Q0010180005000700062Q004C000600043Q0010180005000800060030260005000900030010180005000A00032Q004C000600014Q004C000700024Q00580006000600070010180005000B00062Q004F00066Q004C000700053Q00207900070007000C0012730009000D4Q008200070009000200207900070007000E00120D0009000F4Q0024000A00054Q001D0009000A4Q006300073Q00020026290007001B000100100004463Q001B00010004463Q0029000100061C3Q0007000100020004463Q000700012Q004B3Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q00120D000100014Q004C00025Q0020840002000200022Q00650001000200030004463Q000700012Q00243Q00043Q0004463Q0009000100061C00010005000100020004463Q000500012Q002200013Q0005003026000100030004003026000100050006003026000100070002001018000100083Q0030260001000900032Q004C000200013Q00207900020002000A0012730004000B4Q008200020004000200207900020002000C00120D0004000D4Q0024000500014Q001D000400054Q005C00023Q00030026810003001C0001000E0004463Q001C00010026290003001F0001000F0004463Q001F00012Q004F00046Q0031000400023Q0004463Q002100012Q004F000400014Q0031000400024Q004B3Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q004C7Q0020845Q000100060B3Q001500013Q0004463Q0015000100120D3Q00024Q004C00015Q0020840001000100012Q00653Q000200020004463Q0013000100208400050004000300060B0005001300013Q0004463Q001300012Q004C000500013Q002079000500050004001273000700054Q00820005000700020020790005000500062Q0024000700034Q004200050007000100061C3Q0009000100020004463Q000900012Q004B3Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q004C7Q0020795Q0001001273000200024Q00823Q000200020020795Q00032Q00653Q0002000100262900010013000100040004463Q0013000100120D000200054Q00550002000100012Q004C00025Q002079000200020001001273000400024Q00820002000400020020790002000200032Q00650002000200032Q0024000100034Q00243Q00023Q0004463Q000600012Q004B3Q00017Q00013Q0003043Q007469636B010C4Q004C00025Q00065A3Q0006000100020004463Q0006000100120D000200014Q0047000200014Q006800026Q004C000200014Q002400036Q001000046Q001900026Q006800026Q004B3Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q002200015Q00120D000200014Q002400036Q00650002000200040004463Q000F000100120D000700024Q0024000800064Q00450007000200020026290007000E000100030004463Q000E000100120D000700044Q0024000800064Q00450007000200022Q0024000600074Q007B00010005000600061C00020005000100020004463Q000500012Q0031000100024Q004B3Q00019Q003Q00034Q004C00016Q0031000100024Q004B3Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00208400023Q000100208400033Q00022Q002E0002000200030020840003000100010020840004000100022Q002E00030003000400064100030009000100020004463Q000900012Q002800026Q004F000200014Q0031000200024Q004B3Q00017Q00013Q0003043Q004E616D6500064Q004C8Q004C000100013Q0020840001000100012Q004C000200024Q00423Q000200012Q004B3Q00017Q00013Q0003053Q00737061776E00043Q00120D3Q00013Q00025F00016Q00083Q000200012Q004B3Q00013Q00013Q003E3Q0003083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D6503113Q00506574537061776E65724C6F6164696E67030E3Q0049676E6F7265477569496E7365742Q0103063Q00506172656E7403043Q0067616D65030A3Q004765745365727669636503073Q00436F726547756903053Q004672616D6503043Q0053697A6503053Q005544696D32026Q00F03F028Q0003083Q00506F736974696F6E03103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742026Q003440030F3Q00426F7264657253697A65506978656C03083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D03083Q0055495374726F6B65030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203053Q00436F6C6F72025Q00C06240025Q00E06F4003093Q00546869636B6E652Q73030A3Q0055494772616469656E74030D3Q00436F6C6F7253657175656E636503153Q00436F6C6F7253657175656E63654B6579706F696E74026Q003E40026Q00494003093Q00546578744C6162656C026Q004E40026Q33D33F03163Q004261636B67726F756E645472616E73706172656E637903043Q005465787403133Q00487567652048756E746572204C6F6164696E6703043Q00466F6E74030A3Q00467265646F6B614F6E6503083Q005465787453697A65026Q004440030A3Q0054657874436F6C6F723302E17A14AE47E1DA3F03173Q004C6F6164696E672C20706C6561736520776169743Q2E029A5Q99E93F026Q002E40029A5Q99B93F026Q33E33F030C3Q0054772Q656E5365727669636503063Q0043726561746503093Q0054772Q656E496E666F030B3Q00456173696E675374796C6503063Q004C696E65617203053Q00737061776E03053Q0064656C61790006012Q00120D3Q00013Q0020845Q0002001273000100034Q00453Q000200020030263Q000400050030263Q0006000700120D000100093Q00207900010001000A0012730003000B4Q00820001000300020010183Q0008000100120D000100013Q0020840001000100020012730002000C4Q004500010002000200120D0002000E3Q0020840002000200020012730003000F3Q001273000400103Q0012730005000F3Q001273000600104Q00820002000600020010180001000D000200120D0002000E3Q002084000200020002001273000300103Q001273000400103Q001273000500103Q001273000600104Q008200020006000200101800010011000200120D000200133Q002084000200020014001273000300153Q001273000400153Q001273000500154Q0082000200050002001018000100120002003026000100160010001018000100083Q00120D000200013Q002084000200020002001273000300174Q004500020002000200120D000300193Q002084000300030002001273000400103Q001273000500104Q008200030005000200101800020018000300101800020008000100120D000300013Q0020840003000300020012730004001A4Q004500030002000200101800030008000100120D0004001C3Q00208400040004001B00208400040004001D0010180003001B000400120D000400133Q002084000400040014001273000500103Q0012730006001F3Q001273000700204Q00820004000700020010180003001E000400302600030021000F00120D000400013Q002084000400040002001273000500224Q004500040002000200120D000500233Q0020840005000500022Q0022000600013Q00120D000700243Q002084000700070002001273000800103Q00120D000900133Q002084000900090014001273000A00253Q001273000B00253Q001273000C00254Q00120009000C4Q006300073Q000200120D000800243Q0020840008000800020012730009000F3Q00120D000A00133Q002084000A000A0014001273000B00263Q001273000C00263Q001273000D00264Q0012000A000D4Q004300086Q003B00063Q00012Q00450005000200020010180004001E000500101800040008000100120D000500013Q002084000500050002001273000600274Q004500050002000200120D0006000E3Q0020840006000600020012730007000F3Q001273000800103Q001273000900103Q001273000A00284Q00820006000A00020010180005000D000600120D0006000E3Q002084000600060002001273000700103Q001273000800103Q001273000900293Q001273000A00104Q00820006000A00020010180005001100060030260005002A000F0030260005002B002C00120D0006001C3Q00208400060006002D00208400060006002E0010180005002D00060030260005002F003000120D000600133Q002084000600060014001273000700203Q001273000800203Q001273000900204Q008200060009000200101800050031000600101800050008000100120D000600013Q002084000600060002001273000700274Q004500060002000200120D0007000E3Q0020840007000700020012730008000F3Q001273000900103Q001273000A00103Q001273000B00304Q00820007000B00020010180006000D000700120D0007000E3Q002084000700070002001273000800103Q001273000900103Q001273000A00323Q001273000B00104Q00820007000B00020010180006001100070030260006002A000F0030260006002B003300120D0007001C3Q00208400070007002D00208400070007002E0010180006002D00070030260006002F002500120D000700133Q002084000700070014001273000800203Q001273000900203Q001273000A00204Q00820007000A000200101800060031000700101800060008000100120D000700013Q0020840007000700020012730008000C4Q004500070002000200120D0008000E3Q002084000800080002001273000900343Q001273000A00103Q001273000B00103Q001273000C00354Q00820008000C00020010180007000D000800120D0008000E3Q002084000800080002001273000900363Q001273000A00103Q001273000B00373Q001273000C00104Q00820008000C000200101800070011000800120D000800133Q002084000800080014001273000900303Q001273000A00303Q001273000B00304Q00820008000B000200101800070012000800101800070008000100120D000800013Q0020840008000800020012730009000C4Q004500080002000200120D0009000E3Q002084000900090002001273000A00363Q001273000B00103Q001273000C000F3Q001273000D00104Q00820009000D00020010180008000D000900120D000900133Q002084000900090014001273000A00103Q001273000B001F3Q001273000C00204Q00820009000C000200101800080012000900101800080008000700120D000900093Q00207900090009000A001273000B00384Q00820009000B0002001273000A00253Q002079000B000900392Q0024000D00083Q00120D000E003A3Q002084000E000E00022Q0024000F000A3Q00120D0010001C3Q00208400100010003B00208400100010003C2Q0082000E001000022Q0022000F3Q000100120D0010000E3Q0020840010001000020012730011000F3Q001273001200103Q0012730013000F3Q001273001400104Q0082001000140002001018000F000D00102Q0082000B000F0002000632000C3Q000100012Q002C3Q000B4Q004F000D5Q000632000E0001000100022Q002C3Q000D4Q002C3Q00063Q00120D000F003D4Q00240010000E4Q0008000F00020001000632000F0002000100042Q002C3Q00094Q002C3Q00014Q002C3Q00054Q002C3Q00064Q00240010000C4Q005500100001000100120D0010003E4Q00240011000A4Q00240012000F4Q00420010001200012Q004B3Q00013Q00033Q00013Q0003043Q00506C617900044Q004C7Q0020795Q00012Q00083Q000200012Q004B3Q00017Q00073Q0003043Q005465787403143Q004C6F6164696E672C20706C65617365207761697403043Q0077616974026Q00E03F03153Q004C6F6164696E672C20706C6561736520776169742E03163Q004C6F6164696E672C20706C6561736520776169742Q2E03173Q004C6F6164696E672C20706C6561736520776169743Q2E00254Q004C7Q0006673Q0024000100010004463Q002400012Q004C3Q00013Q0030263Q0001000200120D3Q00033Q001273000100044Q00083Q000200012Q004C7Q00060B3Q000C00013Q0004463Q000C00012Q004B3Q00014Q004C3Q00013Q0030263Q0001000500120D3Q00033Q001273000100044Q00083Q000200012Q004C7Q00060B3Q001500013Q0004463Q001500012Q004B3Q00014Q004C3Q00013Q0030263Q0001000600120D3Q00033Q001273000100044Q00083Q000200012Q004C7Q00060B3Q001E00013Q0004463Q001E00012Q004B3Q00014Q004C3Q00013Q0030263Q0001000700120D3Q00033Q001273000100044Q00083Q000200010004465Q00012Q004B3Q00017Q00123Q0003093Q0054772Q656E496E666F2Q033Q006E6577026Q00F83F03043Q00456E756D030B3Q00456173696E675374796C6503043Q0051756164030F3Q00456173696E67446972656374696F6E2Q033Q004F757403063Q0043726561746503163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03043Q0053697A6503053Q005544696D32028Q0003103Q00546578745472616E73706172656E637903043Q00506C617903093Q00436F6D706C6574656403073Q00436F2Q6E65637400333Q00120D3Q00013Q0020845Q0002001273000100033Q00120D000200043Q00208400020002000500208400020002000600120D000300043Q0020840003000300070020840003000300082Q00823Q000300022Q004C00015Q0020790001000100092Q004C000300014Q002400046Q002200053Q00020030260005000A000B00120D0006000D3Q0020840006000600020012730007000E3Q0012730008000E3Q0012730009000E3Q001273000A000E4Q00820006000A00020010180005000C00062Q00820001000500022Q004C00025Q0020790002000200092Q004C000400024Q002400056Q002200063Q00010030260006000F000B2Q00820002000600022Q004C00035Q0020790003000300092Q004C000500034Q002400066Q002200073Q00010030260007000F000B2Q00820003000700020020790004000100102Q00080004000200010020790004000200102Q00080004000200010020790004000300102Q000800040002000100208400040001001100207900040004001200063200063Q000100012Q002B3Q00014Q00420004000600012Q004B3Q00013Q00013Q00013Q0003073Q0044657374726F7900044Q004C7Q0020795Q00012Q00083Q000200012Q004B3Q00017Q00", GetFEnv(), ...);
