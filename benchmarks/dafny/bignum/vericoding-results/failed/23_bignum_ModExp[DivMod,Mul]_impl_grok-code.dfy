ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
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
method StrToInt(s: string) returns (result: nat)
  requires ValidBitString(s)
  decreases |s|
  ensures result == Str2Int(s)
{
  if |s| == 0 {
    return 0;
  } else {
    var rec := StrToInt(s[0..|s|-1]);
    return 2 * rec + (if s[|s|-1] == '1' then 1 else 0);
  }
}

method IntToBitString(n: nat) returns (result: string)
  requires true
  decreases n
  ensures ValidBitString(result) && Str2Int(result) == n
{
  if n == 0 {
    return "";
  } else {
    var rec := IntToBitString(n / 2);
    return rec + (if n % 2 == 1 then "1" else "0");
  }
}

method PowMod(base: nat, exp: nat, mod: nat) returns (result: nat)
  requires exp >= 0 && mod > 1
  requires true
  decreases exp
  ensures result == Exp_int(base, exp) % mod
{
  var b := base % mod;
  if exp == 0 {
    return 1 % mod;
  } else if exp % 2 == 0 {
    var rec := PowMod(b * b % mod, exp / 2, mod);
    return rec;
  } else {
    var rec := PowMod(b * b % mod, (exp - 1) / 2, mod);
    return rec * (b % mod) % mod;
  }
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
    var x_int := StrToInt(sx);
    var y_int := StrToInt(sy);
    var m_int := StrToInt(sz);
    var result_int := PowMod(x_int, y_int, m_int);
    var res := IntToBitString(result_int);
    return res;
}
// </vc-code>

