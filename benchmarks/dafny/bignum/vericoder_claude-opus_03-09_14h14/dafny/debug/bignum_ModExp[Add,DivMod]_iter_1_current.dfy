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

// <vc-helpers>
method IsEven(s: string) returns (even: bool)
  requires ValidBitString(s)
  ensures even == (Str2Int(s) % 2 == 0)
{
  if |s| == 0 {
    even := true;
  } else {
    even := s[|s|-1] == '0';
  }
}

method DivBy2(s: string) returns (res: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) / 2
{
  if |s| == 1 {
    res := "";
  } else {
    res := s[0..|s|-1];
  }
}

method SubOne(s: string) returns (res: string)
  requires ValidBitString(s)
  requires Str2Int(s) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) - 1
{
  if |s| == 0 {
    res := "";
  } else if s == "1" {
    res := "";
  } else if s[|s|-1] == '1' {
    res := s[0..|s|-1] + "0";
  } else {
    var prefix := SubOne(s[0..|s|-1]);
    res := prefix + "1";
  }
}

method MulMod(s1: string, s2: string, modulus: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(modulus)
  requires Str2Int(modulus) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == (Str2Int(s1) * Str2Int(s2)) % Str2Int(modulus)
{
  // First multiply s1 and s2
  var product := "";
  var temp := s1;
  var multiplier := s2;
  
  // Binary multiplication
  while multiplier != "" && Str2Int(multiplier) > 0
    invariant ValidBitString(temp) && ValidBitString(multiplier) && ValidBitString(product)
    decreases Str2Int(multiplier)
  {
    var isOdd := false;
    if |multiplier| > 0 && multiplier[|multiplier|-1] == '1' {
      isOdd := true;
    }
    
    if isOdd {
      product := Add(product, temp);
    }
    
    temp := Add(temp, temp);  // Double temp
    
    if |multiplier| == 1 {
      multiplier := "";
    } else {
      multiplier := multiplier[0..|multiplier|-1];  // Divide by 2
    }
  }
  
  // Now take modulo
  var q, r := DivMod(product, modulus);
  res := r;
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
  if |sy| == 0 || Str2Int(sy) == 0 {
    res := "1";  // x^0 = 1
    var q, r := DivMod(res, sz);
    res := r;
  } else if sy == "1" {
    // x^1 mod z = x mod z
    var q, r := DivMod(sx, sz);
    res := r;
  } else {
    var even := IsEven(sy);
    if even {
      // y is even: x^y mod z = (x^(y/2))^2 mod z
      var halfY := DivBy2(sy);
      var temp := ModExp(sx, halfY, sz);
      res := MulMod(temp, temp, sz);
    } else {
      // y is odd: x^y mod z = x * x^(y-1) mod z
      var yMinusOne := SubOne(sy);
      var temp := ModExp(sx, yMinusOne, sz);
      res := MulMod(sx, temp, sz);
    }
  }
}
// </vc-code>

