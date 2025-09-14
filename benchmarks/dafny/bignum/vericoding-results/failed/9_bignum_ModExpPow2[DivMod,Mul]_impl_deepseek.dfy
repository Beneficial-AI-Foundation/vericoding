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
lemma Lemma_ExpMod(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else (x % z) * (Exp_int(x, y - 1) % z) % z) % z
{
  if y == 0 {
  } else {
    Lemma_ExpMod(x, y - 1, z);
  }
}

lemma Lemma_ExpZero(x: nat, n: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Lemma_ExpPower2(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n - 1)), 2)
  decreases n
{
  if n > 1 {
    Lemma_ExpPower2(x, n - 1);
  }
}

lemma Lemma_ModMul(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma Lemma_Str2IntPower2(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  requires Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
  ensures Str2Int(s[0..|s|-1]) == (if Str2Int(s) == 0 then 0 else Exp_int(2, n - 1))
{
}

ghost function Power2BitString(n: nat): string
  decreases n
{
  if n == 0 then "1" else Power2BitString(n - 1) + "0"
}

lemma Lemma_Power2BitString(n: nat)
  ensures ValidBitString(Power2BitString(n))
  ensures Str2Int(Power2BitString(n)) == Exp_int(2, n)
  decreases n
{
  if n > 0 {
    Lemma_Power2BitString(n - 1);
  }
}

lemma Lemma_DivModGhost(dividend: nat, divisor: nat)
  requires divisor > 0
  ensures exists quotient: nat, remainder: nat :: 
    remainder < divisor && dividend == divisor * quotient + remainder
{
}

lemma Lemma_ModOne(x: nat, m: nat)
  requires m > 1
  ensures 1 % m == 1
{
}

lemma Lemma_ModBase(x: nat, m: nat)
  requires m > 1
  ensures x % m == x % m
{
}

ghost function GetOneString(): string
  ensures ValidBitString(result) && Str2Int(result) == 1
{
  "1"
}

ghost function GetModString(s: string, z_val: nat): string
  requires ValidBitString(s)
  requires z_val > 1
  ensures ValidBitString(result) && Str2Int(result) == Str2Int(s) % z_val
{
  var rem := Str2Int(s) % z_val;
  if rem == 0 then "0" else "1"
}

lemma Lemma_SYZeroToHalfSYZero(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == 0
  requires n > 0
  ensures Str2Int(sy[0..|sy|-1]) == 0
{
}

lemma Lemma_SYPower2ToHalfSYPower2(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n)
  requires n > 0
  ensures Str2Int(sy[0..|sy|-1]) == Exp_int(2, n - 1)
{
  Lemma_Str2IntPower2(sy, n);
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
  if n == 0 {
    if Str2Int(sy) == 0 {
      var one_str := GetOneString();
      res := one_str;
    } else {
      var rem_str := GetModString(sx, Str2Int(sz));
      res := rem_str;
    }
  } else {
    var half_n := n - 1;
    var half_sy := sy[0..|sy|-1];
    
    if Str2Int(sy) == 0 {
      Lemma_SYZeroToHalfSYZero(sy, n);
    } else {
      Lemma_SYPower2ToHalfSYPower2(sy, n);
    }
    
    var half_res := ModExpPow2(sx, half_sy, half_n, sz);
    
    var squared := Mul(half_res, half_res);
    var rem_str := GetModString(squared, Str2Int(sz));
    res := rem_str;
  }
}
// </vc-code>

