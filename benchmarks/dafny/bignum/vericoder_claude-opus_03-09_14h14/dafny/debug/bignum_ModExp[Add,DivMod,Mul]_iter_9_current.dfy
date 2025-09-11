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
      == { Exp_int_square(x, half); }
      Exp_int(x * x, half);
    }
  }
}

lemma Exp_int_square(x: nat, y: nat)
  ensures Exp_int(x, y) * Exp_int(x, y) == Exp_int(x * x, y)
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x * x, 0) == 1;
  } else {
    calc {
      Exp_int(x, y) * Exp_int(x, y);
      == (x * Exp_int(x, y-1)) * (x * Exp_int(x, y-1));
      == x * x * (Exp_int(x, y-1) * Exp_int(x, y-1));
      == { Exp_int_square(x, y-1); }
      x * x * Exp_int(x * x, y-1);
      == Exp_int(x * x, y);
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
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x, 0) == 1;
    calc {
      Exp_int(x, 1) % z;
      == x % z;
      == (x % z) * 1 % z;
      == (x % z) * (Exp_int(x, 0) % z) % z;
    }
  } else {
    calc {
      Exp_int(x, y) % z;
      == (x * Exp_int(x, y - 1)) % z;
      == ((x % z) * (Exp_int(x, y - 1) % z)) % z;
    }
  }
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

lemma DivByTwoDecreases(sy: string)
  requires ValidBitString(sy)
  requires |sy| > 0
  requires Str2Int(sy) > 1
  ensures Str2Int(sy) / 2 < Str2Int(sy)
  ensures Str2Int(sy) / 2 > 0
{
  assert Str2Int(sy) >= 2;
  assert Str2Int(sy) / 2 >= 1;
}

lemma QuotientNonEmpty(sy: string, quotient: string)
  requires ValidBitString(sy) && ValidBitString(quotient)
  requires |sy| > 0 && Str2Int(sy) > 1
  requires Str2Int(quotient) == Str2Int(sy) / 2
  ensures |quotient| > 0
{
  assert Str2Int(quotient) >= 1;
  if |quotient| == 0 {
    assert Str2Int(quotient) == 0;
    assert false;
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
  // Base case: y == 0
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
  
  // Base case: y == 1
  if sy == "1" {
    var _, r := DivMod(sx, sz);
    res := r;
    OneStringCorrect();
    Exp_int_one(Str2Int(sx));
    return;
  }
  
  // Recursive case: divide y by 2
  TwoStringCorrect();
  var quotient, remainder := DivMod(sy, "10");
  
  assert Str2Int(quotient) == Str2Int(sy) / 2;
  assert Str2Int(remainder) == Str2Int(sy) % 2;
  assert Str2Int(remainder) == 0 || Str2Int(remainder) == 1;
  
  // Since sy > 1, quotient >= 1
  DivByTwoDecreases(sy);
  QuotientNonEmpty(sy, quotient);
  
  // Check if y is even (remainder == 0)
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
    
    var xSquared := Mul(sx, sx);
    var _, xSquaredMod := DivMod(xSquared, sz);
    
    assert |quotient| > 0;
    res := ModExp(xSquaredMod, quotient, sz);
    Exp_int_even(Str2Int(sx), Str2Int(sy));
  } else {
    // y is odd: compute x * x^(y-1) mod z
    assert !IsZeroString(remainder);
    assert Str2Int(remainder) != 0;
    assert Str2Int(remainder) == Str2Int(sy) % 2;
    assert Str2Int(sy) % 2 == 1;
    assert Str2Int(remainder) == 1;
    
    // For y odd, y-1 is even, so we can use the even case
    // First compute x mod z
    var _, xMod := DivMod(sx, sz);
    
    // Compute x^(y-1) mod z by recursion
    // Since y is odd and > 1, y-1 is even and >= 2
    // y-1 = 2 * ((y-1)/2) = 2 * floor(y/2) = 2 * quotient
    var yMinus1 := Mul(quotient, "10");
    var expYMinus1 := ModExp(sx, yMinus1, sz);
    
    // Compute (x mod z) * (x^(y-1) mod z) mod z
    var product := Mul(xMod, expYMinus1);
    var _, r := DivMod(product, sz);
    res := r;
    
    Exp_int_odd(Str2Int(sx), Str2Int(sy));
    ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  }
}
// </vc-code>

