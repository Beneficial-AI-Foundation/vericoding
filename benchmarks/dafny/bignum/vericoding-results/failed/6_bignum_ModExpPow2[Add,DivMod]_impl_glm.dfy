ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := 0;
  var result := "";
  var i := |s1| - 1;
  var j := |s2| - 1;
  
  while i >= 0 || j >= 0 || carry > 0
  {
    var digit1 := if i >= 0 then (if s1[i] == '1' then 1 else 0) else 0;
    var digit2 := if j >= 0 then (if s2[j] == '1' then 1 else 0) else 0;
    var sum := digit1 + digit2 + carry;
    carry := sum / 2;
    result := if sum % 2 == 1 then "1" + result else "0" + result;
    i := i - 1;
    j := j - 1;
  }
  
  res := result;
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  var current := s1;
  while Str2Int(current) >= Str2Int(s2)
  {
    var temp := s2;
    var shifted := "1";
    while Str2Int(temp) <= Str2Int(current) / 2
    {
      temp := temp + "0";
      shifted := shifted + "0";
    }
    current := Add(current, temp);
  }
  res := current;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var product := "0";
  var i := |s1| - 1;
  while i >= 0
  {
    var shifted := s2;
    var j := 0;
    while j < |s1| - 1 - i
    {
      shifted := shifted + "0";
      j := j + 1;
    }
    if s1[i] == '1'
    {
      product := Add(product, shifted);
    }
    i := i - 1;
  }
  res := product;
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  var current := "0";
  quotient := "";
  var i := 0;
  while i < |dividend|
  {
    current := current + dividend[i];
    var q_digit := "0";
    while Str2Int(current) >= Str2Int(divisor)
    {
      current := Add(current, divisor);
      q_digit := Add(q_digit, "1");
    }
    quotient := quotient + q_digit;
    i := i + 1;
  }
  remainder := current;
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if sx == "1" {
      return if Str2Int(sz) == 2 then "1" else "0";
    } else {
      return "0";
    }
  }
  
  var half_exp := ModExpPow2(sx, sy[0..|sy|-1], n-1, sz);
  var squared := Mul(half_exp, half_exp);
  var modulus_squared := Mod(squared, sz);
  
  if sy[|sy|-1] == '1' {
    var product := Mul(modulus_squared, sx);
    return Mod(product, sz);
  } else {
    return modulus_squared;
  }
}
// </vc-code>

