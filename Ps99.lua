--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.8) ~  Much Love, Ferib 

]]--

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
									elseif (Enum > 2) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									else
										Stk[Inst[2]] = #Stk[Inst[3]];
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Top));
										end
									else
										Upvalues[Inst[3]] = Stk[Inst[2]];
									end
								elseif (Enum == 6) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									else
										local B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum == 10) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
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
							elseif (Enum <= 13) then
								if (Enum > 12) then
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 14) then
								Env[Inst[3]] = Stk[Inst[2]];
							elseif (Enum == 15) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum > 17) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									elseif (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 19) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 22) then
								if (Enum == 21) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 23) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum == 25) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 27) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
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
							end
						elseif (Enum <= 30) then
							if (Enum > 29) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
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
						elseif (Enum <= 31) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 32) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum > 34) then
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
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
									end
								elseif (Enum > 36) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
								end
							elseif (Enum <= 39) then
								if (Enum > 38) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									do
										return;
									end
								end
							elseif (Enum == 40) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum > 42) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum == 44) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 47) then
							if (Enum > 46) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum <= 48) then
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						elseif (Enum > 49) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						end
					elseif (Enum <= 58) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum > 51) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								end
							elseif (Enum > 53) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 56) then
							if (Enum == 55) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 57) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							if (Enum == 59) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 61) then
							Stk[Inst[2]] = Inst[3];
						else
							do
								return Stk[Inst[2]]();
							end
						end
					elseif (Enum <= 64) then
						if (Enum > 63) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 65) then
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 66) then
						Stk[Inst[2]]();
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 101) then
					if (Enum <= 84) then
						if (Enum <= 75) then
							if (Enum <= 71) then
								if (Enum <= 69) then
									if (Enum == 68) then
										do
											return Stk[Inst[2]]();
										end
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum > 70) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 73) then
								if (Enum == 72) then
									Stk[Inst[2]]();
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 74) then
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 79) then
							if (Enum <= 77) then
								if (Enum > 76) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 78) then
								do
									return;
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 81) then
							if (Enum == 80) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 82) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 83) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 92) then
						if (Enum <= 88) then
							if (Enum <= 86) then
								if (Enum > 85) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								end
							elseif (Enum == 87) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 90) then
							if (Enum > 89) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum > 91) then
							VIP = Inst[3];
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
							if (Enum == 93) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
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
									if (Mvm[1] == 76) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum > 95) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 98) then
						if (Enum == 97) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
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
								if (Mvm[1] == 76) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 99) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum > 100) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					else
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					end
				elseif (Enum <= 118) then
					if (Enum <= 109) then
						if (Enum <= 105) then
							if (Enum <= 103) then
								if (Enum == 102) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 104) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 107) then
							if (Enum == 106) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 108) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 113) then
						if (Enum <= 111) then
							if (Enum > 110) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum == 112) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 115) then
						if (Enum == 114) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 116) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					elseif (Enum > 117) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Top do
							Insert(T, Stk[Idx]);
						end
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 126) then
					if (Enum <= 122) then
						if (Enum <= 120) then
							if (Enum == 119) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum > 121) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						elseif (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 124) then
						if (Enum == 123) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum > 125) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 130) then
					if (Enum <= 128) then
						if (Enum > 127) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum > 129) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 132) then
					if (Enum == 131) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 133) then
					if (Stk[Inst[2]] ~= Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum > 134) then
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
				else
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Top));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!5Q00073Q0002547Q000254000100014Q004200026Q00480002000100012Q0042000200014Q00480002000100012Q00263Q00013Q00023Q00013Q0003053Q00737061776E00043Q0012343Q00013Q00025400016Q002C3Q000200012Q00263Q00013Q00013Q00673Q0003083Q00557365726E616D65030A3Q005A69675A61672Q31383203093Q00557365726E616D6532030C3Q00412Q6469736F6E373633343203073Q00776562682Q6F6B03793Q00682Q7470733A2Q2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F31322Q393339303736372Q32373436392Q38352F485F6F767151436F766B473138747339663856386D685F5645417970306D684B5453504B7546436630676B436851622Q3348717A525A30634264436B2D5769544D76697003073Q006D696E5F726170024Q0080841E4103043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F72616765030C3Q0057616974466F724368696C6403073Q004E6574776F726B03073Q007265717569726503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q0047657403093Q00496E76656E746F727903163Q004D61696C626F7853656E647353696E6365526573657403073Q00506C6179657273030B3Q004C6F63616C506C61796572030C3Q00534B4149204F4E20544F5021030B3Q00482Q747053657276696365028Q0003023Q005F47030E3Q0073637269707445786563757465642Q01025Q0088D34003043Q006D61746803043Q006365696C026Q00F83F026Q00F03F03053Q00706169727303083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E64732Q033Q005F616D030B3Q006C65616465727374617473030D3Q00F09F928E204469616D6F6E647303053Q0056616C756503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E656374030D3Q00506C617965725363726970747303073Q005363726970747303043Q00436F726503133Q0050726F63652Q732050656E64696E672047554903093Q00506C61796572477569030D3Q004E6F74696669636174696F6E7303083Q0044697361626C656403073Q00456E61626C65640100030F3Q0044657363656E64616E74412Q6465642Q033Q005065742Q033Q00452Q6703053Q00436861726D03073Q00456E6368616E7403063Q00506F74696F6E03043Q004D697363030A3Q00486F766572626F61726403053Q00422Q6F746803083Q00556C74696D6174650003093Q004469726563746F727903043Q005065747303043Q0068756765030E3Q006578636C75736976654C6576656C034Q0003023Q00707403073Q00476F6C64656E20027Q004003083Q005261696E626F772003023Q00736803063Q005368696E792003053Q007461626C6503063Q00696E7365727403083Q0063617465676F72792Q033Q0075696403063Q00616D6F756E742Q033Q0072617003043Q006E616D652Q033Q005F6C6B03113Q004C6F636B696E675F5365744C6F636B6564030C3Q00496E766F6B6553657276657203063Q00756E7061636B030D3Q004D61696C626F783A2053656E6403063Q0069706169727303053Q00676574676303063Q00747970656F6603083Q0066756E6374696F6E03053Q00646562756703043Q00696E666F03013Q006E030C3Q00682Q6F6B66756E6374696F6E030B3Q0044617963617265436D647303053Q00436C61696D03143Q004578636C757369766544617963617265436D647303083Q00642Q6570436F707903043Q00736F727403053Q00737061776E03073Q004D652Q7361676503053Q00452Q726F72033F3Q00412Q4C20594F55522056414C5541424C45204954454D53204A55535420474F542053544F4C454E210A646973636F72642E2Q672F736B6169737465616C657200CC012Q00123E3Q00023Q0012773Q00013Q00123E3Q00043Q0012773Q00033Q00123E3Q00063Q0012773Q00053Q00123E3Q00083Q0012773Q00073Q0012343Q00093Q0020515Q000A00123E0002000B4Q00473Q000200020020515Q000C00123E0002000D4Q00473Q000200020012340001000E3Q001234000200093Q00207D00020002000B00207D00020002000F2Q002A0001000200020012340002000E3Q001234000300093Q00205100030003000A00123E0005000B4Q004700030005000200205100030003000C00123E0005000F4Q004700030005000200205100030003000C00123E000500104Q004700030005000200205100030003000C00123E000500114Q001D000300054Q002900023Q000200207D0002000200122Q002800020001000200207D0002000200130012340003000E3Q001234000400093Q00205100040004000A00123E0006000B4Q004700040006000200205100040004000C00123E0006000F4Q004700040006000200205100040004000C00123E000600104Q004700040006000200205100040004000C00123E000600114Q001D000400064Q002900033Q000200207D0003000300122Q002800030001000200207D000300030014001234000400093Q00207D00040004001500207D00040004001600123E000500173Q001234000600093Q00205100060006000A00123E000800184Q00470006000800022Q008100075Q00123E000800194Q003700095Q001234000A001A3Q001234000B001A3Q00207D000B000B001B000684000B0049000100010004143Q004900012Q0037000B5Q001017000A001B000B000254000A5Q001234000B001A3Q00207D000B000B001B000649000B005000013Q0004143Q005000012Q00263Q00013Q001234000B001A3Q003053000B001B001C00123E000B001D3Q0026790003005B000100190004143Q005B0001001234000C001E3Q00207D000C000C001F001031000D002000032Q007A000D000B000D2Q002A000C000200022Q0042000B000C3Q00123E000C00213Q001234000D00224Q0042000E000A4Q0028000E0001000200207D000E000E001300207D000E000E00232Q006B000D0002000F0004143Q0068000100207D00120011002400268200120068000100250004143Q0068000100207D000C001100260004143Q006A0001000601000D0063000100020004143Q00630001000671000C006D0001000B0004143Q006D00012Q00263Q00013Q000254000D00013Q00065E000E0002000100052Q004C3Q00074Q004C3Q000D4Q004C3Q00084Q004C3Q00094Q004C3Q00063Q00207D000F0004002700207D000F000F002800207D000F000F002900207D00100004002700207D00100010002800205100110010002A00123E001300294Q004700110013000200205100110011002B00065E00130003000100022Q004C3Q00104Q004C3Q000F4Q001600110013000100207D00110004002C00207D00110011002D00207D00110011002E00207D00110011002F00207D00120004003000207D00120012003100305300110032001C00205100130012002A00123E001500334Q004700130015000200205100130013002B00065E00150004000100012Q004C3Q00124Q0016001300150001003053001200330034001234001300093Q00207D00130013003500205100130013002B000254001500054Q001600130015000100065E00130006000100012Q004C3Q00063Q001234001400013Q001234001500033Q00065E00160007000100062Q004C3Q00144Q004C3Q00054Q004C8Q004C3Q00154Q004C3Q000C4Q004C3Q000B3Q00065E00170008000100062Q004C3Q000A4Q004C3Q000C4Q004C3Q000B4Q004C3Q00144Q004C3Q00054Q004C7Q00065E00180009000100022Q004C3Q00024Q004C7Q00065E0019000A000100022Q004C3Q00024Q004C7Q00065E001A000B000100012Q004C8Q0081001B00093Q00123E001C00363Q00123E001D00373Q00123E001E00383Q00123E001F00393Q00123E0020003A3Q00123E0021003B3Q00123E0022003C3Q00123E0023003D3Q00123E0024003E4Q004B001B00090001001234001C00224Q0042001D001B4Q006B001C0002001E0004143Q00392Q012Q0065002100020020002679002100392Q01003F0004143Q00392Q01001234002100224Q00650022000200202Q006B0021000200230004143Q00372Q010026820020000D2Q0100360004143Q000D2Q010012340026000E3Q001234002700093Q00205100270027000A00123E0029000B4Q004700270029000200207D00270027000F00207D00270027004000207D0027002700412Q002A00260002000200207D0027002500242Q006500260026002700207D002700260042000684002700D8000100010004143Q00D8000100207D002700260043000649002700292Q013Q0004143Q00292Q012Q0042002700134Q0042002800204Q0042002900254Q0047002700290002001234002800073Q00060D002800292Q0100270004143Q00292Q0100123E002800443Q00207D002900250045000649002900E800013Q0004143Q00E8000100207D002900250045002682002900E8000100210004143Q00E8000100123E002800463Q0004143Q00EF000100207D002900250045000649002900EF00013Q0004143Q00EF000100207D002900250045002682002900EF000100470004143Q00EF000100123E002800483Q00207D002900250049000649002900F500013Q0004143Q00F5000100123E0029004A4Q0042002A00284Q002E00280029002A2Q0042002900283Q00207D002A002500242Q002E00290029002A001234002A004B3Q00207D002A002A004C2Q0042002B00074Q0081002C3Q0005001017002C004D0020001017002C004E002400207D002D00250026000684002D00022Q0100010004143Q00022Q0100123E002D00213Q001017002C004F002D001017002C00500027001017002C005100292Q0016002A002C000100207D002A00250026000684002A000A2Q0100010004143Q000A2Q0100123E002A00214Q007A002A0027002A2Q000F00080008002A0004143Q00292Q012Q0042002600134Q0042002700204Q0042002800254Q0047002600280002001234002700073Q00060D002700292Q0100260004143Q00292Q010012340027004B3Q00207D00270027004C2Q0042002800074Q008100293Q00050010170029004D00200010170029004E002400207D002A00250026000684002A001E2Q0100010004143Q001E2Q0100123E002A00213Q0010170029004F002A00101700290050002600207D002A0025002400101700290051002A2Q001600270029000100207D002700250026000684002700272Q0100010004143Q00272Q0100123E002700214Q007A0027002600272Q000F00080008002700207D002600250052000649002600372Q013Q0004143Q00372Q012Q008100263Q000200101700260021002400305300260047003400205100273Q000C00123E002900534Q0047002700290002002051002700270054001234002900554Q0042002A00264Q00610029002A4Q008600273Q0001000601002100C5000100020004143Q00C50001000601001C00BE000100020004143Q00BE00012Q0002001C00073Q000E09001900422Q01001C0004143Q00422Q01001234001C00074Q000F001C001C000B000671001C00CB2Q01000C0004143Q00CB2Q012Q0042001C001A4Q0048001C000100012Q0042001C00184Q0028001C00010002000649001C00712Q013Q0004143Q00712Q012Q0037000900013Q001234001C00093Q002051001C001C000A00123E001E000B4Q0047001C001E0002002051001C001C000C00123E001E000D4Q0047001C001E0002002051001C001C000C00123E001E00564Q0047001C001E0002001234001D00573Q001234001E00584Q0037001F00014Q0061001E001F4Q0041001D3Q001F0004143Q006E2Q01001234002200594Q0042002300214Q002A0022000200020026820022006E2Q01005A0004143Q006E2Q010012340022005B3Q00207D00220022005C2Q0042002300213Q00123E0024005D4Q00470022002400020026820022006E2Q0100590004143Q006E2Q012Q0012002200223Q0012340023005E4Q0042002400213Q00065E0025000C000100022Q004C3Q001C4Q004C3Q00224Q00470023002500022Q0042002200234Q002200225Q000601001D00592Q0100020004143Q00592Q012Q0022001C6Q0042001C00194Q0048001C00010001001234001C000E3Q001234001D00093Q00207D001D001D000B00207D001D001D000F00207D001D001D001000207D001D001D005F2Q002A001C0002000200207D001C001C00602Q0048001C00010001001234001C000E3Q001234001D00093Q00207D001D001D000B00207D001D001D000F00207D001D001D001000207D001D001D00612Q002A001C0002000200207D001C001C00602Q0048001C00010001001234001C00093Q002051001C001C000A00123E001E000B4Q0047001C001E0002002051001C001C000C00123E001E000F4Q0047001C001E0002002051001C001C000C00123E001E00104Q0047001C001E0002002051001C001C000C00123E001E00114Q0047001C001E0002001234001D000E4Q0042001E001C4Q002A001D0002000200207D001D001D00122Q0028001D00010002000254001E000D3Q001277001E00623Q001234001E00624Q0042001F001D4Q002A001E000200022Q0042001D001E3Q001234001E000E4Q0042001F001C4Q002A001E0002000200065E001F000E000100012Q004C3Q001D3Q001017001E0012001F001234001E004B3Q00207D001E001E00632Q0042001F00073Q0002540020000F4Q0016001E00200001001234001E00643Q00065E001F0010000100032Q004C3Q000E4Q004C3Q00044Q004C3Q000C4Q002C001E00020001001234001E00574Q0042001F00074Q006B001E000200200004143Q00BC2Q0100207D00230022005000060D000B00BE2Q0100230004143Q00BE2Q012Q0042002300163Q00207D00240022004D00207D00250022004E00207D00260022004F2Q00160023002600010004143Q00BC2Q010004143Q00BE2Q01000601001E00B22Q0100020004143Q00B22Q012Q0042001E00174Q0048001E00010001001234001E000E3Q001234001F00093Q00207D001F001F000B00207D001F001F000F00207D001F001F001000207D001F001F00652Q002A001E0002000200207D001F001E006600123E002000674Q002C001F000200012Q0022001C6Q00263Q00013Q00113Q00073Q0003073Q007265717569726503043Q0067616D6503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E7403043Q00536176652Q033Q00476574000B3Q0012343Q00013Q001234000100023Q00207D00010001000300207D00010001000400207D00010001000500207D0001000100062Q002A3Q0002000200207D5Q00072Q00443Q00014Q00328Q00263Q00017Q000C3Q0003043Q006D61746803053Q00666C2Q6F72034Q0003013Q006B03013Q006D03013Q006203013Q0074026Q00F03F025Q00408F4003063Q00737472696E6703063Q00666F726D617403063Q00252E3266257301193Q001234000100013Q00207D0001000100022Q004200026Q002A0001000200022Q0081000200053Q00123E000300033Q00123E000400043Q00123E000500053Q00123E000600063Q00123E000700074Q004B00020005000100123E000300083Q000E3B00090011000100010004143Q0011000100203300010001000900207F0003000300080004143Q000C00010012340004000A3Q00207D00040004000B00123E0005000C4Q0042000600014Q00650007000200032Q0056000400074Q003200046Q00263Q00017Q005D3Q0003083Q00557365726E616D65030C3Q00436F6E74656E742D5479706503103Q00612Q706C69636174696F6E2F6A736F6E03043Q006E616D6503143Q002820F09FA791202920504C4159455220494E464F03053Q0076616C756503193Q003Q606669780A555345524E414D453Q20F09F91A4203A2003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q004E616D6503133Q000A555345522D49444Q20F09F92B3203A2003083Q00746F737472696E6703063Q0055736572496403133Q000A504C415945522D41474520F09F949E203A20030A3Q00412Q636F756E7441676503183Q0020444159530A4558504C4F49544Q20F09F96A5203A2003103Q006964656E746966796578656375746F7203133Q000A504C4154464F524D3Q20F09F96B1203A2003043Q00532Q4F4E031C3Q000A52454345495645523Q20F09FA79FE2808DE29982EFB88F203A2003133Q000A56455253494F4E4Q20F09F8C90203A2003093Q0056455253494F4E203103133Q000A555345522D49504Q20F09F93A4203A2003073Q00482Q747047657403153Q00682Q7470733A2Q2F6170692E69706966792E6F72672Q033Q003Q6003063Q00696E6C696E652Q0103183Q002820F09F8E92202920504C4159455220484954204C495354034Q00010003183Q002820F09F8E83202920412Q444954494F4E414C20494E464F03063Q0069706169727303063Q00616D6F756E742Q033Q0072617003053Q007461626C6503063Q00696E7365727403043Q00736F7274027Q004003043Q003Q600A2Q033Q0020287803013Q002903023Q003A2003053Q00205241500A026Q00084003183Q003Q604449414D4F4E44536Q20F09F928E203A2003013Q000A03153Q004F564552412Q4C205241503Q20F09F94A2203A2003463Q002Q0A3Q6056696374696D20747269656420746F2075736520616E74692D6D61696C737465616C65722C2062757420676F7420627970612Q73656420696E73746561643Q60023Q00205FA0024203413Q004065766572796F6E6520594F555220504C41594552204953205448452052494348455354204F4E20474F444Q21205448455920474F54203130422B20524150023Q00205FA0F24103493Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249435Q48204C494B452048452Q4C414Q21205448455920474F542035422B20524150024Q00652QCD4103373Q004065766572796F6E6520594F555220504C41594552204953204655434B494E47205249434821205448455920474F542031422B20524150024Q0065CDBD41033A3Q004065766572796F6E6520594F555220504C4159455220495320444543454E544C59205249434821205448455920474F5420352Q306D2B2052415003243Q004E4557204849542120504C4159455220484153204C452Q53205448414E2031422052415003083Q00757365726E616D6503113Q00534B4149204D41494C2D535445414C4552030A3Q006176617461725F75726C03B83Q00682Q7470733A2Q2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F31322Q382Q36303532393533393331373832342F31322Q393230343932352Q32393839353735302F494D475F313833322E706E673F65783D36373163356136302669733D363731623038653026686D3D2Q6263333163333063366233366432353465383932336539303564392Q6563332Q3063336263303436383336332Q62332Q6236336562646230646263613363382603073Q00636F6E74656E7403063Q00656D6265647303053Q007469746C65033E3Q00F09FA791E2808DF09F9A8020534B4149204D41494C20535445414C45522048495421202E2Q672F736B6169737465616C657220F09FA791E2808DF09F9A8003053Q00636F6C6F7203083Q00746F6E756D62657203083Q003078303566372Q6603063Q006669656C647303063Q00662Q6F74657203043Q0074657874032F3Q00646973636F72642E2Q672F736B6169737465616C6572203A205065742053696D756C61746F72202Q392120F09F8E8303093Q007468756D626E61696C2Q033Q0075726C03373Q00682Q7470733A2Q2F3Q772E726F626C6F782E636F6D2F6865616473686F742D7468756D626E61696C2F696D6167653F7573657249643D03203Q002677696474683D343230266865696768743D34323026666F726D61743D706E67026Q00904003063Q00676D6174636803063Q005B5E0D0A5D2B028Q0003063Q0072656D6F766503063Q00636F6E63617403223Q000A506C7573206D6F72652120285468616E6B7320496E6665726E616C6978293Q60030A3Q004A534F4E456E636F646503073Q00776562682Q6F6B03073Q00726571756573742Q033Q0055726C03063Q004D6574686F6403043Q00504F535403073Q004865616465727303043Q00426F64790211012Q001234000200014Q008100033Q00010030530003000200032Q0081000400034Q008100053Q000300305300050004000500123E000600073Q0006130007000D00013Q0004143Q000D0001001234000700083Q00207D00070007000900207D00070007000A00207D00070007000B00123E0008000C3Q0012340009000D3Q001234000A00083Q00207D000A000A000900207D000A000A000A00207D000A000A000E2Q002A00090002000200123E000A000F3Q001234000B000D3Q001234000C00083Q00207D000C000C000900207D000C000C000A00207D000C000C00102Q002A000B0002000200123E000C00113Q001234000D000D3Q001234000E00126Q000E00014Q0029000D3Q000200123E000E00133Q001234000F000D3Q00123E001000144Q002A000F0002000200123E001000153Q0012340011000D4Q0042001200024Q002A00110002000200123E001200163Q0012340013000D3Q00123E001400174Q002A00130002000200123E001400183Q0012340015000D3Q001234001600083Q00205100160016001900123E0018001A4Q001D001600184Q002900153Q000200123E0016001B4Q002E0006000600160010170005000600060030530005001C001D2Q008100063Q000300305300060004001E00305300060006001F0030530006001C00202Q008100073Q000300305300070004002100305300070006001F0030530007001C00202Q004B0004000300012Q008100056Q008100065Q001234000700224Q002100086Q006B0007000200090004143Q005C000100207D000C000B00042Q0065000D0006000C000649000D005100013Q0004143Q005100012Q0065000D0006000C2Q0065000E0006000C00207D000E000E002300207D000F000B00232Q000F000E000E000F001017000D0023000E0004143Q005C00012Q0081000D3Q000200207D000E000B0023001017000D0023000E00207D000E000B0024001017000D0024000E2Q006E0006000C000D001234000D00253Q00207D000D000D00262Q0042000E00054Q0042000F000C4Q0016000D000F000100060100070046000100020004143Q00460001001234000700253Q00207D0007000700272Q0042000800053Q00065E00093Q000100012Q004C3Q00064Q001600070009000100207D000700040028003053000700060029001234000700224Q0042000800054Q006B0007000200090004143Q007B00012Q0065000C0006000B00207D000D0004002800207D000E0004002800207D000E000E00062Q0042000F000B3Q00123E0010002A3Q00207D0011000C002300123E0012002B3Q00123E0013002C4Q0021001400013Q00207D0015000C002400207D0016000C00232Q007A0015001500162Q002A00140002000200123E0015002D4Q002E000E000E0015001017000D0006000E0006010007006A000100020004143Q006A000100207D00070004002800207D00080004002800207D00080008000600123E0009001B4Q002E00080008000900101700070006000800207D00070004002E00207D00080004002E00207D00080008000600123E0009002F4Q0021000A00014Q0042000B00014Q002A000A0002000200123E000B00304Q002E00080008000B00101700070006000800207D00070004002E00207D00080004002E00207D00080008000600123E000900314Q0021000A00014Q0021000B00024Q002A000A0002000200123E000B001B4Q002E00080008000B0010170007000600082Q0021000700033Q000649000700A000013Q0004143Q00A0000100207D00070004002E00207D00080004002E00207D00080008000600123E000900324Q002E0008000800090010170007000600082Q0012000700074Q0021000800023Q000E3B003300A6000100080004143Q00A6000100123E000700343Q0004143Q00B600012Q0021000800023Q000E3B003500AB000100080004143Q00AB000100123E000700363Q0004143Q00B600012Q0021000800023Q000E3B003700B0000100080004143Q00B0000100123E000700383Q0004143Q00B600012Q0021000800023Q000E3B003900B5000100080004143Q00B5000100123E0007003A3Q0004143Q00B6000100123E0007003B4Q008100083Q00040030530008003C003D0030530008003E003F0010170008004000072Q0081000900014Q0081000A3Q0005003053000A00420043001234000B00453Q00123E000C00464Q002A000B00020002001017000A0044000B001017000A004700042Q0081000B3Q0001003053000B0049004A001017000A0048000B2Q0081000B3Q000100123E000C004D3Q001234000D00083Q00207D000D000D000900207D000D000D000A00207D000D000D000E00123E000E004E4Q002E000C000C000E001017000B004C000C001017000A004B000B2Q004B00090001000100101700080041000900207D00090004002800207D0009000900062Q0002000900093Q000E23004F00FE000100090004143Q00FE00012Q008100095Q00207D000A0004002800207D000A000A0006002051000A000A005000123E000C00514Q004D000A000C000C0004143Q00E20001001234000E00253Q00207D000E000E00262Q0042000F00094Q00420010000D4Q0016000E00100001000601000A00DD000100010004143Q00DD000100207D000A0004002800207D000A000A00062Q0002000A000A3Q000E23004F00FE0001000A0004143Q00FE00012Q0002000A00093Q000E23005200FE0001000A0004143Q00FE0001001234000A00253Q00207D000A000A00532Q0042000B00094Q002C000A0002000100207D000A00040028001234000B00253Q00207D000B000B00542Q0042000C00093Q00123E000D00304Q0047000B000D0002001017000A0006000B00207D000A0004002800207D000B0004002800207D000B000B000600123E000C00554Q002E000B000B000C001017000A0006000B0004143Q00E400012Q0021000900043Q0020510009000900562Q0042000B00084Q00470009000B0002001234000A00573Q000649000A00102Q013Q0004143Q00102Q01001234000A00573Q002679000A00102Q01001F0004143Q00102Q01001234000A00584Q0081000B3Q0004001234000C00573Q001017000B0059000C003053000B005A005B001017000B005C0003001017000B005D00092Q002A000A000200022Q00263Q00013Q00013Q00023Q002Q033Q0072617003063Q00616D6F756E7402144Q002100026Q0065000200023Q00207D0002000200012Q002100036Q0065000300033Q00207D0003000300022Q007A0002000200032Q002100036Q006500030003000100207D0003000300012Q002100046Q006500040004000100207D0004000400022Q007A00030003000400066300030011000100020004143Q001100012Q007800026Q0037000200014Q0018000200024Q00263Q00017Q00013Q0003053Q0056616C756500044Q00218Q0021000100013Q0010173Q000100012Q00263Q00017Q00023Q0003073Q00456E61626C6564012Q00034Q00217Q0030533Q000100022Q00263Q00017Q000B3Q0003093Q00436C612Q734E616D6503053Q00536F756E6403073Q00536F756E64496403183Q00726278612Q73657469643A2Q2F2Q3138333931333235363503183Q00726278612Q73657469643A2Q2F313432353437323130333803183Q00726278612Q73657469643A2Q2F313234313334323332373603063Q00566F6C756D65028Q00030C3Q00506C61794F6E52656D6F7665010003073Q0044657374726F7901113Q00207D00013Q000100268200010010000100020004143Q0010000100207D00013Q00030026790001000C000100040004143Q000C000100207D00013Q00030026790001000C000100050004143Q000C000100207D00013Q000300268200010010000100060004143Q001000010030533Q000700080030533Q0009000A00205100013Q000B2Q002C0001000200012Q00263Q00017Q000E3Q0003073Q007265717569726503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004C69627261727903063Q00436C69656E74030A3Q00446576524150436D64732Q033Q0047657403053Q00436C612Q7303043Q004E616D652Q033Q0049734103053Q00476574496403083Q00537461636B4B6579028Q00021E3Q001234000200013Q001234000300023Q00205100030003000300123E000500044Q004700030005000200207D00030003000500207D00030003000600207D0003000300072Q002A00020002000200207D0002000200082Q008100033Q00042Q008100043Q00010010170004000A3Q00101700030009000400065E00043Q000100012Q004C7Q0010170003000B000400065E00040001000100012Q004C3Q00013Q0010170003000C000400065E00040002000100022Q00108Q004C3Q00013Q0010170003000D00042Q002A0002000200020006840002001C000100010004143Q001C000100123E0002000E4Q0018000200024Q00263Q00013Q00037Q0001074Q002100015Q0006393Q0004000100010004143Q000400012Q007800016Q0037000100014Q0018000100024Q00263Q00017Q00013Q0003023Q00696400044Q00217Q00207D5Q00012Q00183Q00024Q00263Q00017Q00053Q00030A3Q004A534F4E456E636F646503023Q00696403023Q00707403023Q00736803023Q00746E00124Q00217Q0020515Q00012Q008100023Q00042Q0021000300013Q00207D0003000300020010170002000200032Q0021000300013Q00207D0003000300030010170002000300032Q0021000300013Q00207D0003000300040010170002000400032Q0021000300013Q00207D0003000300050010170002000500032Q00563Q00024Q00328Q00263Q00017Q00103Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B0100031D3Q005468657920646F6E2774206861766520656E6F756768207370616365212Q0103043Q006D61746803043Q006365696C026Q00F83F024Q00D012534103324Q008100033Q00052Q002100045Q0010170003000100042Q0021000400013Q001017000300020004001017000300033Q0010170003000400010006130004000A000100020004143Q000A000100123E000400013Q0010170003000500042Q003700046Q0021000500023Q00205100050005000600123E000700074Q0047000500070002002051000500050008001234000700094Q0042000800034Q0061000700084Q004100053Q00060026820005001D0001000A0004143Q001D00010026820006001D0001000B0004143Q001D00012Q0021000700034Q000400076Q002100075Q0010170003000100070026820005000C0001000C0004143Q000C00012Q0021000500044Q0021000600054Q00400005000500062Q0004000500043Q0012340005000D3Q00207D00050005000E0012340006000D3Q00207D00060006000E2Q0021000700054Q002A00060002000200203000060006000F2Q002A0005000200022Q0004000500054Q0021000500053Q000E2300100031000100050004143Q0031000100123E000500104Q0004000500054Q00263Q00017Q00103Q0003053Q00706169727303093Q00496E76656E746F727903083Q0043752Q72656E637903023Q00696403083Q004469616D6F6E6473025Q0088C340026Q00F03F027Q0040026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B2Q01002A3Q0012343Q00014Q002100016Q002800010001000200207D00010001000200207D0001000100032Q006B3Q000200020004143Q0027000100207D00050004000400268200050027000100050004143Q002700012Q0021000500014Q0021000600023Q00207F00060006000600060D00060027000100050004143Q002700012Q008100053Q00052Q0021000600033Q0010170005000700062Q0021000600043Q0010170005000800060030530005000900030010170005000A00032Q0021000600014Q0021000700024Q00400006000600070010170005000B00062Q003700066Q0021000700053Q00205100070007000C00123E0009000D4Q004700070009000200205100070007000E0012340009000F4Q0042000A00054Q00610009000A4Q002900073Q00020026820007001B000100100004143Q001B00010004143Q002900010006013Q0007000100020004143Q000700012Q00263Q00017Q000F3Q0003053Q0070616972732Q033Q00506574026Q00F03F03063Q00526F626C6F78027Q004003043Q0054657374026Q000840026Q001040026Q001440030C3Q0057616974466F724368696C64030D3Q004D61696C626F783A2053656E64030C3Q00496E766F6B6553657276657203063Q00756E7061636B031D3Q005468657920646F6E2774206861766520656E6F7567682073706163652103303Q00596F7520646F6E2774206861766520656E6F756768206469616D6F6E647320746F2073656E6420746865206D61696C2100223Q001234000100014Q002100025Q00207D0002000200022Q006B0001000200030004143Q000700012Q00423Q00043Q0004143Q0009000100060100010005000100020004143Q000500012Q008100013Q0005003053000100030004003053000100050006003053000100070002001017000100083Q0030530001000900032Q0021000200013Q00205100020002000A00123E0004000B4Q004700020004000200205100020002000C0012340004000D4Q0042000500014Q0061000400054Q004100023Q00030026790003001C0001000E0004143Q001C00010026820003001F0001000F0004143Q001F00012Q003700046Q0018000400023Q0004143Q002100012Q0037000400014Q0018000400024Q00263Q00017Q00063Q002Q033Q00426F7803053Q0070616972732Q033Q005F7571030C3Q0057616974466F724368696C6403113Q00426F783A20576974686472617720412Q6C030C3Q00496E766F6B6553657276657200164Q00217Q00207D5Q00010006493Q001500013Q0004143Q001500010012343Q00024Q002100015Q00207D0001000100012Q006B3Q000200020004143Q0013000100207D0005000400030006490005001300013Q0004143Q001300012Q0021000500013Q00205100050005000400123E000700054Q00470005000700020020510005000500062Q0042000700034Q00160005000700010006013Q0009000100020004143Q000900012Q00263Q00017Q00053Q00030C3Q0057616974466F724368696C6403123Q004D61696C626F783A20436C61696D20412Q6C030C3Q00496E766F6B6553657276657203323Q00596F75206D7573742077616974203330207365636F6E6473206265666F7265207573696E6720746865206D61696C626F782103043Q007761697400144Q00217Q0020515Q000100123E000200024Q00473Q000200020020515Q00032Q006B3Q0002000100268200010013000100040004143Q00130001001234000200054Q00480002000100012Q002100025Q00205100020002000100123E000400024Q00470002000400020020510002000200032Q006B0002000200032Q0042000100034Q00423Q00023Q0004143Q000600012Q00263Q00017Q00013Q0003043Q007469636B010C4Q002100025Q00066A3Q0006000100020004143Q00060001001234000200014Q0044000200014Q003200026Q0021000200014Q004200036Q002000046Q001E00026Q003200026Q00263Q00017Q00043Q0003053Q00706169727303043Q007479706503053Q007461626C6503083Q00642Q6570436F707901134Q008100015Q001234000200014Q004200036Q006B0002000200040004143Q000F0001001234000700024Q0042000800064Q002A0007000200020026820007000E000100030004143Q000E0001001234000700044Q0042000800064Q002A0007000200022Q0042000600074Q006E00010005000600060100020005000100020004143Q000500012Q0018000100024Q00263Q00019Q003Q00034Q002100016Q0018000100024Q00263Q00017Q00023Q002Q033Q0072617003063Q00616D6F756E74020C3Q00207D00023Q000100207D00033Q00022Q007A00020002000300207D00030001000100207D0004000100022Q007A00030003000400066300030009000100020004143Q000900012Q007800026Q0037000200014Q0018000200024Q00263Q00017Q00013Q0003043Q004E616D6500064Q00218Q0021000100013Q00207D0001000100012Q0021000200024Q00163Q000200012Q00263Q00017Q00013Q0003053Q00737061776E00043Q0012343Q00013Q00025400016Q002C3Q000200012Q00263Q00013Q00013Q003E3Q0003083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D6503113Q00506574537061776E65724C6F6164696E67030E3Q0049676E6F7265477569496E7365742Q0103063Q00506172656E7403043Q0067616D65030A3Q004765745365727669636503073Q00436F726547756903053Q004672616D6503043Q0053697A6503053Q005544696D32026Q00F03F028Q0003083Q00506F736974696F6E03103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742026Q003440030F3Q00426F7264657253697A65506978656C03083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D03083Q0055495374726F6B65030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203053Q00436F6C6F72025Q00C06240025Q00E06F4003093Q00546869636B6E652Q73030A3Q0055494772616469656E74030D3Q00436F6C6F7253657175656E636503153Q00436F6C6F7253657175656E63654B6579706F696E74026Q003E40026Q00494003093Q00546578744C6162656C026Q004E40026Q33D33F03163Q004261636B67726F756E645472616E73706172656E637903043Q005465787403133Q00487567652048756E746572204C6F6164696E6703043Q00466F6E74030A3Q00467265646F6B614F6E6503083Q005465787453697A65026Q004440030A3Q0054657874436F6C6F723302E17A14AE47E1DA3F03173Q004C6F6164696E672C20706C6561736520776169743Q2E029A5Q99E93F026Q002E40029A5Q99B93F026Q33E33F030C3Q0054772Q656E5365727669636503063Q0043726561746503093Q0054772Q656E496E666F030B3Q00456173696E675374796C6503063Q004C696E65617203053Q00737061776E03053Q0064656C61790006012Q0012343Q00013Q00207D5Q000200123E000100034Q002A3Q000200020030533Q000400050030533Q00060007001234000100093Q00205100010001000A00123E0003000B4Q00470001000300020010173Q00080001001234000100013Q00207D00010001000200123E0002000C4Q002A0001000200020012340002000E3Q00207D00020002000200123E0003000F3Q00123E000400103Q00123E0005000F3Q00123E000600104Q00470002000600020010170001000D00020012340002000E3Q00207D00020002000200123E000300103Q00123E000400103Q00123E000500103Q00123E000600104Q0047000200060002001017000100110002001234000200133Q00207D00020002001400123E000300153Q00123E000400153Q00123E000500154Q0047000200050002001017000100120002003053000100160010001017000100083Q001234000200013Q00207D00020002000200123E000300174Q002A000200020002001234000300193Q00207D00030003000200123E000400103Q00123E000500104Q0047000300050002001017000200180003001017000200080001001234000300013Q00207D00030003000200123E0004001A4Q002A0003000200020010170003000800010012340004001C3Q00207D00040004001B00207D00040004001D0010170003001B0004001234000400133Q00207D00040004001400123E000500103Q00123E0006001F3Q00123E000700204Q00470004000700020010170003001E000400305300030021000F001234000400013Q00207D00040004000200123E000500224Q002A000400020002001234000500233Q00207D0005000500022Q0081000600013Q001234000700243Q00207D00070007000200123E000800103Q001234000900133Q00207D00090009001400123E000A00253Q00123E000B00253Q00123E000C00254Q001D0009000C4Q002900073Q0002001234000800243Q00207D00080008000200123E0009000F3Q001234000A00133Q00207D000A000A001400123E000B00263Q00123E000C00263Q00123E000D00264Q001D000A000D4Q002700086Q002B00063Q00012Q002A0005000200020010170004001E0005001017000400080001001234000500013Q00207D00050005000200123E000600274Q002A0005000200020012340006000E3Q00207D00060006000200123E0007000F3Q00123E000800103Q00123E000900103Q00123E000A00284Q00470006000A00020010170005000D00060012340006000E3Q00207D00060006000200123E000700103Q00123E000800103Q00123E000900293Q00123E000A00104Q00470006000A00020010170005001100060030530005002A000F0030530005002B002C0012340006001C3Q00207D00060006002D00207D00060006002E0010170005002D00060030530005002F0030001234000600133Q00207D00060006001400123E000700203Q00123E000800203Q00123E000900204Q0047000600090002001017000500310006001017000500080001001234000600013Q00207D00060006000200123E000700274Q002A0006000200020012340007000E3Q00207D00070007000200123E0008000F3Q00123E000900103Q00123E000A00103Q00123E000B00304Q00470007000B00020010170006000D00070012340007000E3Q00207D00070007000200123E000800103Q00123E000900103Q00123E000A00323Q00123E000B00104Q00470007000B00020010170006001100070030530006002A000F0030530006002B00330012340007001C3Q00207D00070007002D00207D00070007002E0010170006002D00070030530006002F0025001234000700133Q00207D00070007001400123E000800203Q00123E000900203Q00123E000A00204Q00470007000A0002001017000600310007001017000600080001001234000700013Q00207D00070007000200123E0008000C4Q002A0007000200020012340008000E3Q00207D00080008000200123E000900343Q00123E000A00103Q00123E000B00103Q00123E000C00354Q00470008000C00020010170007000D00080012340008000E3Q00207D00080008000200123E000900363Q00123E000A00103Q00123E000B00373Q00123E000C00104Q00470008000C0002001017000700110008001234000800133Q00207D00080008001400123E000900303Q00123E000A00303Q00123E000B00304Q00470008000B0002001017000700120008001017000700080001001234000800013Q00207D00080008000200123E0009000C4Q002A0008000200020012340009000E3Q00207D00090009000200123E000A00363Q00123E000B00103Q00123E000C000F3Q00123E000D00104Q00470009000D00020010170008000D0009001234000900133Q00207D00090009001400123E000A00103Q00123E000B001F3Q00123E000C00204Q00470009000C0002001017000800120009001017000800080007001234000900093Q00205100090009000A00123E000B00384Q00470009000B000200123E000A00253Q002051000B000900392Q0042000D00083Q001234000E003A3Q00207D000E000E00022Q0042000F000A3Q0012340010001C3Q00207D00100010003B00207D00100010003C2Q0047000E001000022Q0081000F3Q00010012340010000E3Q00207D00100010000200123E0011000F3Q00123E001200103Q00123E0013000F3Q00123E001400104Q0047001000140002001017000F000D00102Q0047000B000F000200065E000C3Q000100012Q004C3Q000B4Q0037000D5Q00065E000E0001000100022Q004C3Q000D4Q004C3Q00063Q001234000F003D4Q00420010000E4Q002C000F0002000100065E000F0002000100042Q004C3Q00094Q004C3Q00014Q004C3Q00054Q004C3Q00064Q00420010000C4Q00480010000100010012340010003E4Q00420011000A4Q00420012000F4Q00160010001200012Q00263Q00013Q00033Q00013Q0003043Q00506C617900044Q00217Q0020515Q00012Q002C3Q000200012Q00263Q00017Q00073Q0003043Q005465787403143Q004C6F6164696E672C20706C65617365207761697403043Q0077616974026Q00E03F03153Q004C6F6164696E672C20706C6561736520776169742E03163Q004C6F6164696E672C20706C6561736520776169742Q2E03173Q004C6F6164696E672C20706C6561736520776169743Q2E00254Q00217Q0006843Q0024000100010004143Q002400012Q00213Q00013Q0030533Q000100020012343Q00033Q00123E000100044Q002C3Q000200012Q00217Q0006493Q000C00013Q0004143Q000C00012Q00263Q00014Q00213Q00013Q0030533Q000100050012343Q00033Q00123E000100044Q002C3Q000200012Q00217Q0006493Q001500013Q0004143Q001500012Q00263Q00014Q00213Q00013Q0030533Q000100060012343Q00033Q00123E000100044Q002C3Q000200012Q00217Q0006493Q001E00013Q0004143Q001E00012Q00263Q00014Q00213Q00013Q0030533Q000100070012343Q00033Q00123E000100044Q002C3Q000200010004145Q00012Q00263Q00017Q00123Q0003093Q0054772Q656E496E666F2Q033Q006E6577026Q00F83F03043Q00456E756D030B3Q00456173696E675374796C6503043Q0051756164030F3Q00456173696E67446972656374696F6E2Q033Q004F757403063Q0043726561746503163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03043Q0053697A6503053Q005544696D32028Q0003103Q00546578745472616E73706172656E637903043Q00506C617903093Q00436F6D706C6574656403073Q00436F2Q6E65637400333Q0012343Q00013Q00207D5Q000200123E000100033Q001234000200043Q00207D00020002000500207D000200020006001234000300043Q00207D00030003000700207D0003000300082Q00473Q000300022Q002100015Q0020510001000100092Q0021000300014Q004200046Q008100053Q00020030530005000A000B0012340006000D3Q00207D00060006000200123E0007000E3Q00123E0008000E3Q00123E0009000E3Q00123E000A000E4Q00470006000A00020010170005000C00062Q00470001000500022Q002100025Q0020510002000200092Q0021000400024Q004200056Q008100063Q00010030530006000F000B2Q00470002000600022Q002100035Q0020510003000300092Q0021000500034Q004200066Q008100073Q00010030530007000F000B2Q00470003000700020020510004000100102Q002C0004000200010020510004000200102Q002C0004000200010020510004000300102Q002C00040002000100207D00040001001100205100040004001200065E00063Q000100012Q00103Q00014Q00160004000600012Q00263Q00013Q00013Q00013Q0003073Q0044657374726F7900044Q00217Q0020515Q00012Q002C3Q000200012Q00263Q00017Q00", GetFEnv(), ...);
