ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
// Binary addition helper
method BinaryAdd(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := 0;
  var result := "";
  var i := 0;
  var n1 := |s1|;
  var n2 := |s2|;
  
  while i < n1 || i < n2 || carry > 0
    invariant 0 <= carry <= 1
    invariant ValidBitString(result)
    invariant i >= 0
    decreases (if n1 > i then n1 - i else 0) + (if n2 > i then n2 - i else 0) + carry
  {
    var bit1 := if i < n1 then (if s1[n1 - 1 - i] == '1' then 1 else 0) else 0;
    var bit2 := if i < n2 then (if s2[n2 - 1 - i] == '1' then 1 else 0) else 0;
    var sum := bit1 + bit2 + carry;
    
    carry := sum / 2;
    var bitChar := if sum % 2 == 1 then '1' else '0';
    result := [bitChar] + result;
    i := i + 1;
  }
  
  // Remove leading zeros
  while |result| > 1 && result[0] == '0'
    invariant ValidBitString(result)
    invariant |result| > 0
  {
    result := result[1..];
  }
  
  if |result| == 0 {
    result := "0";
  }
  
  res := result;
}

// Shift left (multiply by 2^n)
method ShiftLeft(s: string, n: nat) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) * Power2(n)
{
  if s == "0" {
    res := "0";
  } else {
    var zeros := "";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant ValidBitString(zeros)
      invariant |zeros| == i
      invariant forall j | 0 <= j < i :: zeros[j] == '0'
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    res := s + zeros;
  }
}

ghost function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  if s1 == "0" || s2 == "0" {
    res := "0";
    return;
  }
  
  var product := "0";
  var i := 0;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(product)
  {
    if s2[|s2| - 1 - i] == '1' {
      var shifted := ShiftLeft(s1, i);
      product := BinaryAdd(product, shifted);
    }
    i := i + 1;
  }
  
  res := product;
}
// </vc-code>

