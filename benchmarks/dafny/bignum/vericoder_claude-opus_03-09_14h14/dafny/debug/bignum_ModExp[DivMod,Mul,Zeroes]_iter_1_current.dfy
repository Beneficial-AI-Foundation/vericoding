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

lemma Exp_int_even(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2)
{
  if y == 2 {
    assert Exp_int(x, 2) == x * x;
    assert Exp_int(x, 1) == x;
  } else {
    Exp_int_even(x, y/2);
  }
}

lemma Exp_int_odd(x: nat, y: nat)
  requires y > 0 && y % 2 == 1
  ensures Exp_int(x, y) == x * Exp_int(x, y/2) * Exp_int(x, y/2)
{
  if y == 1 {
    assert Exp_int(x, 1) == x;
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_int_even(x, y/2);
  }
}

lemma ModExpCorrectness(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures y % 2 == 0 ==> Exp_int(x, y) % z == (Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z
  ensures y % 2 == 1 ==> Exp_int(x, y) % z == (x % z * ((Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z)) % z
{
  if y % 2 == 0 {
    Exp_int_even(x, y);
    assert Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2);
  } else {
    Exp_int_odd(x, y);
    assert Exp_int(x, y) == x * Exp_int(x, y/2) * Exp_int(x, y/2);
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
  // Check if sy is "0" (base case)
  var isZero := true;
  var i := 0;
  while i < |sy|
    invariant 0 <= i <= |sy|
    invariant isZero == AllZero(sy[0..i])
  {
    if sy[i] != '0' {
      isZero := false;
    }
    i := i + 1;
  }
  
  if isZero {
    // Return "1"
    res := "1";
    return;
  }
  
  // Divide sy by 2
  var two := "10";
  var syDiv2, syMod2 := DivMod(sy, two);
  
  // Recursive call
  var halfPower := ModExp(sx, syDiv2, sz);
  
  // Square the result
  var squared := Mul(halfPower, halfPower);
  
  // Take mod z
  var squaredMod, _ := DivMod(squared, sz);
  squaredMod := squared[|squaredMod|..];
  
  // Check if sy is odd (syMod2 == "1")
  var isOdd := |syMod2| > 0 && syMod2[|syMod2|-1] == '1';
  
  if isOdd {
    // Multiply by sx and take mod again
    var temp := Mul(squaredMod, sx);
    var quotient, remainder := DivMod(temp, sz);
    res := remainder;
  } else {
    res := squaredMod;
  }
  
  // Apply correctness lemmas
  ModExpCorrectness(Str2Int(sx), Str2Int(sy), Str2Int(sz));
}
// </vc-code>

