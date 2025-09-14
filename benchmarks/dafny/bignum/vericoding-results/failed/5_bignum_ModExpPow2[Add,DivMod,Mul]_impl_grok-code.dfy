ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method ModExpBase(base: string, pow: nat, mod: string) returns (r: string)
  requires ValidBitString(base) && ValidBitString(mod)
  requires Str2Int(mod) >= 2
  ensures ValidBitString(r)
  ensures Str2Int(r) == (Exp_int(Str2Int(base), pow)) % Str2Int(mod)
  decreases pow
{
  if pow == 0 {
    r := "1";
  } else {
    var half := ModExpBase(base, pow / 2, mod);
    var sq := Mul(half, half);
    var quot, rem := DivMod(sq, mod);
    var result := rem;
    if pow % 2 == 1 {
      var mul := Mul(result, base);
      var quot2, rem2 := DivMod(mul, mod);
      result := rem2;
    }
    r := result;
  }
}

function Exp_int(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if |sy| == 1 && sy == "0" {
    res := "1";
  } else {
    res := ModExpBase(sx, Exp_int(2, n), sz);
  }
}
// </vc-code>

