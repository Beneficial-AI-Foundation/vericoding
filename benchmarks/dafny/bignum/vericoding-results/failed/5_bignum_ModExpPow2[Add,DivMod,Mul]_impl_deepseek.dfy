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
lemma LemmaStr2IntAppend(s: string, c: char)
  requires ValidBitString(s) && (c == '0' || c == '1')
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

lemma LemmaModExp(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (Exp_int(x, y / 2) % z) * (Exp_int(x, y / 2) % z) * (if y % 2 == 1 then x % z else 1) % z
  decreases y
{
  if y == 0 {
  } else if y == 1 {
  } else {
    LemmaModExp(x, y / 2, z);
  }
}

lemma LemmaExpIntPower2(n: nat, k: nat)
  ensures Exp_int(2, n) * Exp_int(2, k) == Exp_int(2, n + k)
  decreases n
{
  if n > 0 {
    LemmaExpIntPower2(n - 1, k);
  }
}

lemma LemmaStr2IntLengthPower2(s: string, n: nat)
  requires ValidBitString(s) && Str2Int(s) == Exp_int(2, n) && |s| == n + 1
  ensures s[0] == '1' && forall i | 1 <= i < |s| :: s[i] == '0'
  decreases s
{
}

lemma LemmaMulMod(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma LemmaAddMod(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a + b) % m == ((a % m) + (b % m)) % m
{
}

ghost function ModExpPow2Helper(sx: string, sy: string, n: nat, sz: string): string
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(result)
  ensures Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  if Str2Int(sy) == 0 then
    "1"
  else if n == 0 then
    var x_val := Str2Int(sx) % Str2Int(sz);
    if x_val == 0 then "0" else "1"
  else
    var half_n := n - 1;
    var half_sy := sy[0..|sy|-1];
    assert ValidBitString(half_sy);
    var half_res := ModExpPow2Helper(sx, half_sy, half_n, sz);
    assert Str2Int(half_res) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz);
    var square := Mul(half_res, half_res);
    var mod_square := DivMod(square, sz).1;
    if sy[|sy|-1] == '1' then
      var temp := Mul(mod_square, sx);
      var mod_temp := DivMod(temp, sz).1;
      mod_temp
    else
      mod_square
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
  if Str2Int(sy) == 0 {
    res := "1";
  } else if n == 0 {
    var x_val := Str2Int(sx) % Str2Int(sz);
    if x_val == 0 {
      res := "0";
    } else {
      res := "1";
    }
  } else {
    var half_n := n - 1;
    var half_sy := sy[0..|sy|-1];
    assert ValidBitString(half_sy);
    var half_res := ModExpPow2Helper(sx, half_sy, half_n, sz);
    assert Str2Int(half_res) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz);
    var square := Mul(half_res, half_res);
    var mod_square := DivMod(square, sz).1;
    if sy[|sy|-1] == '1' {
      var temp := Mul(mod_square, sx);
      var mod_temp := DivMod(temp, sz).1;
      res := mod_temp;
    } else {
      res := mod_square;
    }
  }
}
// </vc-code>

