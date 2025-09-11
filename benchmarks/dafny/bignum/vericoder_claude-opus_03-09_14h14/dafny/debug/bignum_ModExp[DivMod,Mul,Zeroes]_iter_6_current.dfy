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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_split(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    calc == {
      Exp_int(x, a + b);
      Exp_int(x, b);
      1 * Exp_int(x, b);
      Exp_int(x, 0) * Exp_int(x, b);
      Exp_int(x, a) * Exp_int(x, b);
    }
  } else {
    calc == {
      Exp_int(x, a + b);
      x * Exp_int(x, a + b - 1);
      { Exp_int_split(x, a - 1, b); }
      x * Exp_int(x, a - 1) * Exp_int(x, b);
      Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2)
{
  assert y == y/2 + y/2;
  Exp_int_split(x, y/2, y/2);
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y/2) * Exp_int(x, y/2)
{
  assert y == 1 + y/2 + y/2;
  calc == {
    Exp_int(x, y);
    { Exp_int_split(x, 1, y/2 + y/2); }
    Exp_int(x, 1) * Exp_int(x, y/2 + y/2);
    { Exp_int_split(x, y/2, y/2); }
    x * Exp_int(x, y/2) * Exp_int(x, y/2);
  }
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures y % 2 == 0 ==> Exp_int(x, y) % z == (Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z
  ensures y % 2 == 1 ==> Exp_int(x, y) % z == (x % z * ((Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z)) % z
{
  if y % 2 == 0 {
    Exp_int_even(x, y);
  } else {
    Exp_int_odd(x, y);
  }
}

lemma AllZeroImpliesZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    assert ValidBitString(s[0..|s|-1]);
    assert AllZero(s[0..|s|-1]);
    AllZeroImpliesZero(s[0..|s|-1]);
    assert s[|s|-1] == '0';
  }
}

lemma NonZeroStringHasNonZeroQuotient(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && !AllZero(s)
  requires Str2Int(s) > 0
  ensures Str2Int(s) / 2 < Str2Int(s)
  ensures Str2Int(s) == 1 || Str2Int(s) / 2 > 0
{
  if Str2Int(s) == 1 {
    assert Str2Int(s) / 2 == 0;
  } else {
    assert Str2Int(s) >= 2;
    assert Str2Int(s) / 2 >= 1;
  }
}

lemma NonZeroNotAllZero(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires !AllZero(s)
  ensures Str2Int(s) > 0
{
  if Str2Int(s) == 0 {
    AllZeroImpliesZero(s);
    assert false;
  }
}

lemma SubstringValidBitString(s: string, i: nat, j: nat)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
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
  // Check if sy is "0" (base case)
  var isZero := true;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant isZero == AllZero(sy[0..i])
    invariant ValidBitString(sy[0..i])
  {
    if sy[i] != '0' {
      isZero := false;
    }
    i := i + 1;
  }
  
  if isZero {
    // Return "1"
    res := "1";
    assert sy[0..|sy|] == sy;
    AllZeroImpliesZero(sy);
    assert Str2Int(sy) == 0;
    Exp_int_zero(Str2Int(sx));
    assert Str2Int("1") == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    return;
  }
  
  // sy is not zero, so Str2Int(sy) > 0
  assert !AllZero(sy);
  NonZeroNotAllZero(sy);
  assert Str2Int(sy) > 0;
  
  // Divide sy by 2
  var two := "10";
  var syDiv2, syMod2 := DivMod(sy, two);
  
  assert Str2Int(two) == 2;
  assert Str2Int(syDiv2) == Str2Int(sy) / 2;
  assert Str2Int(syMod2) == Str2Int(sy) % 2;
  
  NonZeroStringHasNonZeroQuotient(sy);
  
  // Check if syDiv2 is zero (meaning sy was 1)
  if |syDiv2| == 0 || AllZero(syDiv2) {
    if |syDiv2| == 0 {
      assert Str2Int(syDiv2) == 0;
    } else {
      AllZeroImpliesZero(syDiv2);
      assert Str2Int(syDiv2) == 0;
    }
    assert Str2Int(sy) / 2 == 0;
    assert Str2Int(sy) == 1;
    
    // Return sx % sz
    var quotient, remainder := DivMod(sx, sz);
    res := remainder;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    return;
  }
  
  // syDiv2 is not zero, so we can recurse
  assert !(|syDiv2| == 0 || AllZero(syDiv2));
  assert Str2Int(syDiv2) > 0;
  
  // For termination: syDiv2 is smaller than sy
  assert Str2Int(syDiv2) < Str2Int(sy);
  
  // Recursive call
  var halfPower := ModExp(sx, syDiv2, sz);
  
  // Square the result
  var squared := Mul(halfPower, halfPower);
  
  // Take mod z
  var quotient, remainder := DivMod(squared, sz);
  var squaredMod := remainder;
  
  // Check if sy is odd
  var isOdd := false;
  if |syMod2| > 0 && syMod2[|syMod2|-1] == '1' {
    isOdd := true;
    assert Str2Int(syMod2) == 1;
    assert Str2Int(sy) % 2 == 1;
  } else {
    assert Str2Int(syMod2) == 0;
    assert Str2Int(sy) % 2 == 0;
  }
  
  if isOdd {
    // Multiply by sx and take mod again
    var temp := Mul(squaredMod, sx);
    var q2, r2 := DivMod(temp, sz);
    res := r2;
  } else {
    res := squaredMod;
  }
  
  // Apply correctness lemmas
  ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
  
  assert Str2Int(halfPower) == Exp_int(Str2Int(sx), Str2Int(syDiv2)) % Str2Int(sz);
  assert Str2Int(squared) == Str2Int(halfPower) * Str2Int(halfPower);
  assert Str2Int(squaredMod) == Str2Int(squared) % Str2Int(sz);
}
// </vc-code>

