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
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_one(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    Exp_int_mult(x, half, half);
  }
}

lemma Exp_int_mult(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if y == 0 {
    assert Exp_int(x, y + z) == Exp_int(x, z);
    assert Exp_int(x, y) == 1;
  } else {
    Exp_int_mult(x, y - 1, z);
  }
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures (Exp_int(x, y) % z) == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x, 0) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
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
  if Str2Int(sy) == 0 {
    res := "1";
    return;
  }
  
  if Str2Int(sy) == 1 {
    var _, r := DivMod(sx, sz);
    res := r;
    return;
  }
  
  var quotient, remainder := DivMod(sy, "10");
  
  if Str2Int(remainder) == 0 {
    // y is even: compute (x^2)^(y/2) mod z
    var xSquared := Mul(sx, sx);
    var xSquaredMod, _ := DivMod(xSquared, sz);
    res := ModExp(xSquaredMod, quotient, sz);
    Exp_int_even(Str2Int(sx), Str2Int(sy));
  } else {
    // y is odd: compute x * (x^(y-1)) mod z
    var quotientTimes10 := Mul(quotient, "10");
    var yMinus1 := Add(quotientTimes10, "0");
    var expResult := ModExp(sx, yMinus1, sz);
    var product := Mul(sx, expResult);
    var _, r := DivMod(product, sz);
    res := r;
    Exp_int_odd(Str2Int(sx), Str2Int(sy));
    ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  }
}
// </vc-code>

