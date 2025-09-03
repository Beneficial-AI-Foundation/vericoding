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
    calc {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * x * Exp_int(x, 0);
      == x * x * 1;
      == x * x;
      == Exp_int(x * x, 1);
    }
  } else {
    var half := y / 2;
    assert y == 2 * half;
    Exp_int_mult(x, half, half);
    calc {
      Exp_int(x, y);
      == Exp_int(x, half + half);
      == Exp_int(x, half) * Exp_int(x, half);
      == Exp_int(x * x, half);
    }
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
  // Direct proof from definition
}

predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma ZeroStringImpliesZero(s: string)
  requires ValidBitString(s)
  requires IsZeroString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    if |s| > 1 {
      assert IsZeroString(s[0..|s|-1]);
      ZeroStringImpliesZero(s[0..|s|-1]);
    }
  }
}

lemma OneStringCorrect()
  ensures ValidBitString("1")
  ensures Str2Int("1") == 1
{
}

lemma TwoStringCorrect()
  ensures ValidBitString("10")
  ensures Str2Int("10") == 2
{
}

lemma QuotientDecreasesSize(dividend: string, divisor: string, quotient: string)
  requires ValidBitString(dividend) && ValidBitString(divisor) && ValidBitString(quotient)
  requires Str2Int(divisor) > 1
  requires Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  requires Str2Int(dividend) > 1
  ensures |quotient| < |dividend| || (|quotient| == |dividend| && Str2Int(quotient) < Str2Int(dividend))
{
  // This lemma establishes that quotient is smaller than dividend
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
  // Check if y is "1" (base case)
  if sy == "1" {
    var _, r := DivMod(sx, sz);
    res := r;
    OneStringCorrect();
    Exp_int_one(Str2Int(sx));
    return;
  }
  
  // Check if y consists only of zeros (represents 0)
  var allZeros := true;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant allZeros == (forall j | 0 <= j < i :: sy[j] == '0')
  {
    if sy[i] != '0' {
      allZeros := false;
      break;
    }
    i := i + 1;
  }
  
  if allZeros {
    res := "1";
    assert IsZeroString(sy);
    ZeroStringImpliesZero(sy);
    Exp_int_zero(Str2Int(sx));
    return;
  }
  
  // General case: divide by 10 (binary)
  TwoStringCorrect();
  var quotient, remainder := DivMod(sy, "10");
  
  // Since sy > 1 and we divide by 2, quotient will be smaller
  assert Str2Int(sy) > 1; // because sy != "1" and sy != "0"
  assert Str2Int(quotient) == Str2Int(sy) / 2;
  assert Str2Int(remainder) == Str2Int(sy) % 2;
  QuotientDecreasesSize(sy, "10", quotient);
  
  // Check if remainder is "0" (even case)
  var remIsZero := true;
  i := 0;
  while i < |remainder|
    invariant 0 <= i <= |remainder|
    invariant remIsZero == (forall j | 0 <= j < i :: remainder[j] == '0')
  {
    if remainder[i] != '0' {
      remIsZero := false;
      break;
    }
    i := i + 1;
  }
  
  if remIsZero {
    // y is even: compute (x^2)^(y/2) mod z
    assert IsZeroString(remainder);
    ZeroStringImpliesZero(remainder);
    assert Str2Int(remainder) == 0;
    assert Str2Int(sy) % 2 == 0;
    assert Str2Int(sy) > 0;
    
    var xSquared := Mul(sx, sx);
    var _, xSquaredMod := DivMod(xSquared, sz);
    assert |quotient| > 0; // because Str2Int(sy) > 1 and sy is even
    res := ModExp(xSquaredMod, quotient, sz);
    Exp_int_even(Str2Int(sx), Str2Int(sy));
  } else {
    // y is odd: compute x * (x^(y-1)) mod z
    assert !IsZeroString(remainder);
    assert Str2Int(remainder) == 1; // remainder when dividing by 2 is either 0 or 1
    assert Str2Int(sy) % 2 == 1;
    assert Str2Int(sy) > 0;
    
    // y - 1 = quotient * 2
    var yMinus1 := Mul(quotient, "10");
    assert Str2Int(yMinus1) == Str2Int(sy) - 1;
    assert |yMinus1| > 0; // because Str2Int(sy) > 1
    var expResult := ModExp(sx, yMinus1, sz);
    var product := Mul(sx, expResult);
    var _, r := DivMod(product, sz);
    res := r;
    Exp_int_odd(Str2Int(sx), Str2Int(sy));
    ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  }
}
// </vc-code>

