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

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x * 1;
    assert Exp_int(x * x, 1) == x * x * 1;
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

lemma ModExpCorrectness(x: nat, y: nat, z: nat, result: nat)
  requires z > 1
  requires result == Exp_int(x, y) % z
  ensures result == Exp_int(x, y) % z
{
}

predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

predicate IsOneString(s: string) 
  requires ValidBitString(s)
{
  |s| == 1 && s[0] == '1'
}

lemma ZeroStringImpliesZero(s: string)
  requires ValidBitString(s)
  requires IsZeroString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert ValidBitString(prefix);
    assert IsZeroString(prefix);
    ZeroStringImpliesZero(prefix);
    assert Str2Int(prefix) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0 == 0;
  }
}

lemma OneStringImpliesOne(s: string)
  requires ValidBitString(s)
  requires IsOneString(s)
  ensures Str2Int(s) == 1
{
  assert |s| == 1;
  assert s[0] == '1';
  assert s == "1";
  assert Str2Int(s) == Str2Int("1");
  assert Str2Int("1") == 2 * Str2Int("") + 1;
  assert Str2Int("") == 0;
  assert Str2Int(s) == 1;
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
    // sy represents 0
    res := "1";
    assert IsZeroString(sy);
    ZeroStringImpliesZero(sy);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    assert 1 % Str2Int(sz) == 1;
  } else if |sy| == 1 && sy[0] == '1' {
    // sy represents 1
    var _, rem := DivMod(sx, sz);
    res := rem;
    assert IsOneString(sy);
    OneStringImpliesOne(sy);
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
  } else {
    // Check if sy is even (last bit is 0) or odd (last bit is 1)
    if sy[|sy| - 1] == '0' {
      // y is even: compute (x^2)^(y/2) mod z
      var x_squared := Mul(sx, sx);
      var _, x_squared_mod := DivMod(x_squared, sz);
      
      // Divide y by 2 by removing the last '0'
      var y_half := sy[0..|sy| - 1];
      assert ValidBitString(y_half);
      assert Str2Int(sy) % 2 == 0;
      assert Str2Int(y_half) == Str2Int(sy) / 2;
      
      var temp := ModExp(x_squared_mod, y_half, sz);
      res := temp;
      
      ghost var y_val := Str2Int(sy);
      assert y_val > 0;
      assert y_val % 2 == 0;
      Exp_int_even(Str2Int(sx), y_val);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2);
      assert (Exp_int(Str2Int(sx) * Str2Int(sx), Str2Int(sy) / 2) % Str2Int(sz)) == 
             (Exp_int((Str2Int(sx) * Str2Int(sx)) % Str2Int(sz), Str2Int(sy) / 2) % Str2Int(sz));
    } else {
      // y is odd: compute x * x^(y-1) mod z
      var _, x_mod := DivMod(sx, sz);
      
      // Subtract 1 from y by changing last '1' to '0'
      var y_minus_one := sy[0..|sy| - 1] + "0";
      assert ValidBitString(y_minus_one);
      assert Str2Int(y_minus_one) == Str2Int(sy) - 1;
      
      var temp := ModExp(x_mod, y_minus_one, sz);
      var product := Mul(x_mod, temp);
      var _, rem := DivMod(product, sz);
      res := rem;
      
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1);
      assert (Str2Int(sx) * Exp_int(Str2Int(sx), Str2Int(sy) - 1)) % Str2Int(sz) ==
             ((Str2Int(sx) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(sy) - 1) % Str2Int(sz))) % Str2Int(sz);
    }
  }
}
// </vc-code>

