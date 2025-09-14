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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
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
lemma {:induction false} ExpIntLemma(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 0 + z) == Exp_int(x, z);
    assert Exp_int(x, 0) * Exp_int(x, z) == 1 * Exp_int(x, z) == Exp_int(x, z);
  } else {
    ExpIntLemma(x, y - 1, z);
    assert Exp_int(x, y + z) == x * Exp_int(x, y - 1 + z);
    assert Exp_int(x, y) * Exp_int(x, z) == x * Exp_int(x, y - 1) * Exp_int(x, z);
  }
}

lemma ModExpLemma(base: nat, exp: nat, mod: nat)
  requires mod > 1
  ensures Exp_int(base, exp) % mod == (base % mod) * (Exp_int(base, exp - 1) % mod) % mod
{
  if exp > 0 {
  }
}

lemma ZeroExpLemma(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpIntZeroLemma(x: nat)
  ensures Exp_int(0, x) == (if x == 0 then 1 else 0)
  decreases x
{
  if x > 0 {
    ExpIntZeroLemma(x - 1);
  }
}

lemma ModOneLemma(x: nat, m: nat)
  requires m > 1
  ensures 1 % m == 1
{
}

ghost function ValidBitStringSubstring(s: string, from: int, to: int): bool
  requires 0 <= from <= to <= |s|
{
  forall i | from <= i < to :: s[i] == '0' || s[i] == '1'
}

ghost function Str2IntSubstring(s: string, from: int, to: int): nat
  requires 0 <= from <= to <= |s|
  requires ValidBitStringSubstring(s, from, to)
  decreases to - from
{
  if to == from then
    0
  else
    2 * Str2IntSubstring(s, from, to - 1) + (if s[to - 1] == '1' then 1 else 0)
}

lemma SyHalfValid(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 1
  ensures ValidBitString(sy[0..|sy|-1])
{
}

lemma SyHalfValue(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 1
  ensures Str2Int(sy[0..|sy|-1]) == Str2Int(sy) / 2
{
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
  if Str2Int(sy) == 0 {
    var one := Zeros(1);
    one := "1";
    var division_result := DivMod(one, sz);
    res := division_result.remainder;
  } else if |sy| == 1 {
    var division_result := DivMod(sx, sz);
    res := division_result.remainder;
  } else {
    var n := |sy| - 1;
    var sy_half := sy[0..n];
    var res1_str := ModExp(sx, sy_half, sz);
    var res_squared_str := Mul(res1_str, res1_str);
    var division_result := DivMod(res_squared_str, sz);
    res := division_result.remainder;
  }
}
// </vc-code>

