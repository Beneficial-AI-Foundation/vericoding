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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    assert Exp_int(x, a + b) == Exp_int(x, b);
    assert Exp_int(x, a) * Exp_int(x, b) == 1 * Exp_int(x, b) == Exp_int(x, b);
  } else {
    Exp_int_add(x, a - 1, b);
    assert Exp_int(x, a + b) == Exp_int(x, (a - 1) + b + 1);
    assert Exp_int(x, (a - 1) + b + 1) == x * Exp_int(x, (a - 1) + b);
    assert x * Exp_int(x, (a - 1) + b) == x * (Exp_int(x, a - 1) * Exp_int(x, b));
    assert x * (Exp_int(x, a - 1) * Exp_int(x, b)) == (x * Exp_int(x, a - 1)) * Exp_int(x, b);
    assert (x * Exp_int(x, a - 1)) * Exp_int(x, b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

lemma Exp_int_2(x: nat)
  ensures Exp_int(x, 2) == x * x
{
  assert Exp_int(x, 2) == x * Exp_int(x, 1);
  assert Exp_int(x, 1) == x * Exp_int(x, 0);
  assert Exp_int(x, 0) == 1;
  assert Exp_int(x, 1) == x * 1 == x;
  assert Exp_int(x, 2) == x * x;
}

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    Exp_int_2(x);
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x * Exp_int(x * x, 0);
    assert Exp_int(x * x, 0) == 1;
    assert Exp_int(x * x, 1) == x * x;
    assert y / 2 == 1;
    assert Exp_int(x * x, y / 2) == x * x;
  } else {
    assert y >= 2;
    Exp_int_even(x, y - 2);
    assert Exp_int(x, y) == x * x * Exp_int(x, y - 2);
    assert Exp_int(x, y - 2) == Exp_int(x * x, (y - 2) / 2);
    assert (y - 2) / 2 == y / 2 - 1;
    assert Exp_int(x * x, (y - 2) / 2) == Exp_int(x * x, y / 2 - 1);
    assert x * x * Exp_int(x * x, y / 2 - 1) == (x * x) * Exp_int(x * x, y / 2 - 1);
    assert (x * x) * Exp_int(x * x, y / 2 - 1) == Exp_int(x * x, y / 2);
  }
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x * x, (y - 1) / 2)
{
  assert y >= 1;
  assert (y - 1) % 2 == 0;
  if y == 1 {
    assert (y - 1) / 2 == 0;
    assert Exp_int(x * x, 0) == 1;
    assert x * Exp_int(x * x, 0) == x;
    assert Exp_int(x, 1) == x;
  } else {
    Exp_int_even(x, y - 1);
    assert Exp_int(x, y - 1) == Exp_int(x * x, (y - 1) / 2);
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert x * Exp_int(x, y - 1) == x * Exp_int(x * x, (y - 1) / 2);
  }
}

lemma ModMulProperty(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
}

lemma ModExpProperty(x: nat, y: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
  decreases y
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x % z, 0) == 1;
  } else {
    ModExpProperty(x, y - 1, z);
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    assert Exp_int(x % z, y) == (x % z) * Exp_int(x % z, y - 1);
    ModMulProperty(x, Exp_int(x, y - 1), z);
    ModMulProperty(x % z, Exp_int(x % z, y - 1), z);
  }
}

lemma YHalfComputation(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 0
  requires sy[|sy| - 1] == '0'
  ensures ValidBitString(sy[0..|sy| - 1])
  ensures Str2Int(sy[0..|sy| - 1]) == Str2Int(sy) / 2
{
  var y_half := sy[0..|sy| - 1];
  assert ValidBitString(y_half);
  assert Str2Int(sy) == 2 * Str2Int(y_half) + 0;
  assert Str2Int(sy) == 2 * Str2Int(y_half);
  assert Str2Int(y_half) == Str2Int(sy) / 2;
}

lemma YMinusOneHalfComputation(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 0
  requires sy[|sy| - 1] == '1'
  ensures ValidBitString(sy[0..|sy| - 1])
  ensures Str2Int(sy[0..|sy| - 1]) == (Str2Int(sy) - 1) / 2
{
  var y_minus_one_half := sy[0..|sy| - 1];
  assert ValidBitString(y_minus_one_half);
  assert Str2Int(sy) == 2 * Str2Int(y_minus_one_half) + 1;
  assert Str2Int(sy) - 1 == 2 * Str2Int(y_minus_one_half);
  assert Str2Int(y_minus_one_half) == (Str2Int(sy) - 1) / 2;
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
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    assert 1 < Str2Int(sz);
    assert Str2Int(res) == 1 % Str2Int(sz);
  } else if |sy| == 1 && sy[0] == '1' {
    var _, rem := DivMod(sx, sz);
    res := rem;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
  } else {
    assert |sy| > 1;
    
    if sy[|sy| - 1] == '0' {
      // y is even
      var x_squared := Mul(sx, sx);
      var _, x_squared_mod := DivMod(x_squared, sz);
      
      var y_half := sy[0..|sy| - 1];
      YHalfComputation(sy);
      assert Str2Int(y_half) == Str2Int(sy) / 2;
      
      var temp := ModExp(x_squared_mod, y_half, sz);
      res := temp;
      
      Exp_int_even(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
      ModExpProperty(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2, Str2Int(sz));
      assert Str2Int(res) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2) % Str2Int(sz);
      assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    } else {
      // y is odd
      var _, x_mod := DivMod(sx, sz);
      var x_squared := Mul(x_mod, x_mod);
      var _, x_squared_mod := DivMod(x_squared, sz);
      
      var y_minus_one_half := sy[0..|sy| - 1];
      YMinusOneHalfComputation(sy);
      assert Str2Int(y_minus_one_half) == (Str2Int(sy) - 1) / 2;
      
      var temp := ModExp(x_squared_mod, y_minus_one_half, sz);
      var product := Mul(x_mod, temp);
      var _, rem := DivMod(product, sz);
      res := rem;
      
      Exp_int_odd(Str2Int(sx), Str2Int(sy));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx) * Str2Int(sx), (Str2Int(sy) - 1) / 2);
      ModExpProperty(Str2Int(sx), Str2Int(sy), Str2Int(sz));
      ModMulProperty(Str2Int(sx), Exp_int(Str2Int(sx) * Str2Int(sx), (Str2Int(sy) - 1) / 2), Str2Int(sz));
      ModExpProperty(Str2Int(sx) * Str2Int(sx), (Str2Int(sy) - 1) / 2, Str2Int(sz));
      assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  }
}
// </vc-code>

