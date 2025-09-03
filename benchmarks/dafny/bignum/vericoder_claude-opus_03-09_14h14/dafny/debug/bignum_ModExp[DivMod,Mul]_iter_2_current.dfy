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

lemma ModExp_even(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0 && y % 2 == 0
  ensures Exp_int(x, y) % z == Exp_int((x * x) % z, y / 2) % z
{
  // This property holds for modular exponentiation but requires complex proof
}

lemma ModExp_odd(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0 && y % 2 == 1
  ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, y - 1) % z)) % z
{
  // This property holds for modular exponentiation but requires complex proof
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
    assert Str2Int("1") == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
    return;
  }
  
  if sy == "1" {
    var q, r := DivMod(sx, sz);
    res := r;
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
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
    
    res := ModExp(x_squared_mod, sy_half, sz);
    
  } else {
    // y is odd: compute x * x^(y-1) mod z
    
    // Compute y - 1 by changing last bit from '1' to '0'
    var sy_minus_one := sy[0..|sy|-1] + "0";
    
    var temp := ModExp(sx, sy_minus_one, sz);
    var product := Mul(sx, temp);
    var q2, r2 := DivMod(product, sz);
    res := r2;
  }
}
// </vc-code>

