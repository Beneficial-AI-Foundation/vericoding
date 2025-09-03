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
lemma Exp_int_positive(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
    Exp_int_positive(x, y - 1);
  }
}

lemma Exp_int_split(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
  // Follows directly from definition
}

lemma Str2Int_positive(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) >= 0
{
  // Follows from definition of Str2Int
}

lemma Str2Int_even(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '0'
  ensures Str2Int(s) % 2 == 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1])
{
  // Follows from definition of Str2Int
}

lemma Str2Int_odd(s: string)
  requires ValidBitString(s) && |s| > 0 && s[|s|-1] == '1'
  ensures Str2Int(s) % 2 == 1
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1
{
  // Follows from definition of Str2Int
}

lemma Exp_int_square(x: nat)
  ensures Exp_int(x, 2) == x * x
{
  calc == {
    Exp_int(x, 2);
    x * Exp_int(x, 1);
    x * (x * Exp_int(x, 0));
    x * (x * 1);
    x * x;
  }
}

lemma Exp_int_even_split(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
  decreases y
{
  if y == 2 {
    Exp_int_square(x);
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x * x, 1) == x * x * Exp_int(x * x, 0) == x * x;
  } else {
    var half := y / 2;
    assert y == 2 * half;
    assert half > 0;
    assert half % 2 == 0 || half % 2 == 1;
    
    if half % 2 == 0 {
      assert half > 0 && half % 2 == 0;
      Exp_int_even_split(x * x, half);
      assert Exp_int(x * x, half) == Exp_int((x * x) * (x * x), half / 2);
      
      calc == {
        Exp_int(x, y);
        { Exp_int_even_split(x, y); }
        Exp_int(x * x, half);
      }
    } else {
      calc == {
        Exp_int(x, y);
        == { assert y == 2 * half; }
        Exp_int(x, 2 * half);
        == { Exp_int_power_sum(x, half, half); }
        Exp_int(x, half) * Exp_int(x, half);
        == { assert Exp_int(x * x, half) == Exp_int(x, half) * Exp_int(x, half) by {
          Exp_int_power_product(x, x, half);
        }}
        Exp_int(x * x, half);
      }
    }
  }
}

lemma Exp_int_power_sum(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a
{
  if a == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, b) == 1 * Exp_int(x, b);
  } else {
    calc == {
      Exp_int(x, a + b);
      x * Exp_int(x, a + b - 1);
      { assert a + b - 1 == (a - 1) + b; }
      x * Exp_int(x, (a - 1) + b);
      { Exp_int_power_sum(x, a - 1, b); }
      x * (Exp_int(x, a - 1) * Exp_int(x, b));
      (x * Exp_int(x, a - 1)) * Exp_int(x, b);
      Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma Exp_int_power_product(x: nat, y: nat, n: nat)
  ensures Exp_int(x * y, n) == Exp_int(x, n) * Exp_int(y, n)
  decreases n
{
  if n == 0 {
    assert Exp_int(x * y, 0) == 1;
    assert Exp_int(x, 0) * Exp_int(y, 0) == 1 * 1 == 1;
  } else {
    calc == {
      Exp_int(x * y, n);
      (x * y) * Exp_int(x * y, n - 1);
      { Exp_int_power_product(x, y, n - 1); }
      (x * y) * (Exp_int(x, n - 1) * Exp_int(y, n - 1));
      x * (y * Exp_int(x, n - 1)) * Exp_int(y, n - 1);
      x * Exp_int(x, n - 1) * (y * Exp_int(y, n - 1));
      (x * Exp_int(x, n - 1)) * (y * Exp_int(y, n - 1));
      Exp_int(x, n) * Exp_int(y, n);
    }
  }
}

lemma ModExpEvenHelper(x: nat, y: nat, z: nat)
  requires y > 0 && y % 2 == 0 && z > 1
  ensures Exp_int(x, y) % z == Exp_int((x * x) % z, y / 2) % z
  decreases y
{
  var half := y / 2;
  assert y == 2 * half;
  
  Exp_int_even_split(x, y);
  assert Exp_int(x, y) == Exp_int(x * x, half);
  
  calc == {
    Exp_int(x, y) % z;
    Exp_int(x * x, half) % z;
    { if half > 0 { ModExpRecursive(x * x, half, z); } }
    Exp_int((x * x) % z, half) % z;
  }
}

lemma ModExpRecursive(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
  decreases y
{
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x % z, 1) == x % z;
  } else {
    calc == {
      Exp_int(x, y) % z;
      (x * Exp_int(x, y - 1)) % z;
      { ModularMultiplication(x, Exp_int(x, y - 1), z); }
      ((x % z) * (Exp_int(x, y - 1) % z)) % z;
      { ModExpRecursive(x, y - 1, z); }
      ((x % z) * (Exp_int(x % z, y - 1) % z)) % z;
      { ModularMultiplication(x % z, Exp_int(x % z, y - 1), z); }
      ((x % z) * Exp_int(x % z, y - 1)) % z;
      Exp_int(x % z, y) % z;
    }
  }
}

lemma ModExpOddHelper(x: nat, y: nat, z: nat)
  requires y > 0 && y % 2 == 1 && z > 1
  ensures Exp_int(x, y) % z == (x * Exp_int(x, y - 1)) % z
{
  assert Exp_int(x, y) == x * Exp_int(x, y - 1);
}

lemma ModularMultiplication(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // Standard modular arithmetic property
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
  if sy == "0" {
    res := "1";
    return;
  }
  
  if sy == "1" {
    var q, r := DivMod(sx, sz);
    res := r;
    return;
  }
  
  var lastBit := sy[|sy| - 1];
  
  if lastBit == '0' {
    // y is even: compute (x^2)^(y/2) mod z
    var x_squared := Mul(sx, sx);
    var q1, x_squared_mod := DivMod(x_squared, sz);
    
    var sy_half := sy[0..|sy|-1];
    
    Str2Int_even(sy);
    assert Str2Int(sy) == 2 * Str2Int(sy_half);
    assert Str2Int(sy) / 2 == Str2Int(sy_half);
    
    res := ModExp(x_squared_mod, sy_half, sz);
    
    assert Str2Int(x_squared) == Str2Int(sx) * Str2Int(sx);
    assert Str2Int(x_squared_mod) == Str2Int(x_squared) % Str2Int(sz);
    assert Str2Int(x_squared_mod) == (Str2Int(sx) * Str2Int(sx)) % Str2Int(sz);
    assert Str2Int(res) == Exp_int(Str2Int(x_squared_mod), Str2Int(sy_half)) % Str2Int(sz);
    
    ModExpEvenHelper(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    
  } else {
    // y is odd: compute x * x^(y-1) mod z
    var sy_minus_one := sy[0..|sy|-1] + "0";
    
    Str2Int_odd(sy);
    assert Str2Int(sy) == 2 * Str2Int(sy[0..|sy|-1]) + 1;
    
    Str2Int_even(sy_minus_one);
    assert Str2Int(sy_minus_one) == 2 * Str2Int(sy[0..|sy|-1]);
    assert Str2Int(sy_minus_one) == Str2Int(sy) - 1;
    
    var temp := ModExp(sx, sy_minus_one, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(sy_minus_one)) % Str2Int(sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(sy) - 1) % Str2Int(sz);
    
    var product := Mul(sx, temp);
    assert Str2Int(product) == Str2Int(sx) * Str2Int(temp);
    
    var q2, r2 := DivMod(product, sz);
    res := r2;
    
    assert Str2Int(res) == Str2Int(product) % Str2Int(sz);
    assert Str2Int(res) == (Str2Int(sx) * Str2Int(temp)) % Str2Int(sz);
    
    ModExpOddHelper(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    ModularMultiplication(Str2Int(sx), Exp_int(Str2Int(sx), Str2Int(sy) - 1), Str2Int(sz));
  }
}
// </vc-code>

