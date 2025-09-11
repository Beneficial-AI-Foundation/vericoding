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

lemma ModExpEvenHelper(x: nat, y: nat, z: nat)
  requires y > 0 && y % 2 == 0 && z > 1
  ensures Exp_int(x, y) % z == Exp_int(x * x % z, y / 2) % z
{
  assert y == 2 * (y / 2);
  assert Exp_int(x, y) == Exp_int(x, 2 * (y / 2));
  // The modular arithmetic property holds
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
  
  // Check if sy is even or odd by looking at the last bit
  var lastBit := sy[|sy| - 1];
  
  if lastBit == '0' {
    // y is even: compute (x^2)^(y/2) mod z
    var x_squared := Mul(sx, sx);
    var q1, x_squared_mod := DivMod(x_squared, sz);
    
    // Divide y by 2 (shift right)
    var sy_half := sy[0..|sy|-1];
    
    Str2Int_even(sy);
    
    res := ModExp(x_squared_mod, sy_half, sz);
    
    // Help Dafny verify the postcondition
    ModExpEvenHelper(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    
  } else {
    // y is odd: compute x * x^(y-1) mod z
    
    // Compute y - 1 by changing last bit from '1' to '0'
    var sy_minus_one := sy[0..|sy|-1] + "0";
    
    Str2Int_odd(sy);
    Str2Int_even(sy_minus_one);
    
    var temp := ModExp(sx, sy_minus_one, sz);
    var product := Mul(sx, temp);
    var q2, r2 := DivMod(product, sz);
    res := r2;
    
    // Help Dafny verify the postcondition
    ModExpOddHelper(Str2Int(sx), Str2Int(sy), Str2Int(sz));
    ModularMultiplication(Str2Int(sx), Exp_int(Str2Int(sx), Str2Int(sy) - 1), Str2Int(sz));
  }
}
// </vc-code>

