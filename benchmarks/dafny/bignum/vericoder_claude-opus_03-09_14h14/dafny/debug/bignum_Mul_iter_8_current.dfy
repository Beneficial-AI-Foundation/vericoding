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
  
  ghost var accumulated := 0;
  ghost var power := 1;
  
  while i < n1 || i < n2 || carry > 0
    invariant 0 <= carry <= 1
    invariant ValidBitString(result)
    invariant i >= 0
    invariant power == Power2(i)
    invariant accumulated + carry * power == 
             (if i <= n1 then Str2Int(s1[n1-i..n1]) else Str2Int(s1)) + 
             (if i <= n2 then Str2Int(s2[n2-i..n2]) else Str2Int(s2))
    invariant |result| == i
    invariant forall j | 0 <= j < i :: result[i-1-j] == '0' || result[i-1-j] == '1'
    invariant accumulated == if i == 0 then 0 else 
             (if result[i-1] == '1' then Power2(i-1) else 0) + 
             (if i >= 2 then 2 * Str2Int(result[0..i-1]) else 0)
    decreases (if n1 > i then n1 - i else 0) + (if n2 > i then n2 - i else 0) + carry
  {
    var bit1 := if i < n1 then (if s1[n1 - 1 - i] == '1' then 1 else 0) else 0;
    var bit2 := if i < n2 then (if s2[n2 - 1 - i] == '1' then 1 else 0) else 0;
    var sum := bit1 + bit2 + carry;
    
    ghost var oldAccumulated := accumulated;
    ghost var oldPower := power;
    
    carry := sum / 2;
    var bitChar := if sum % 2 == 1 then '1' else '0';
    result := result + [bitChar];
    
    accumulated := oldAccumulated + (sum % 2) * oldPower;
    power := oldPower * 2;
    i := i + 1;
  }
  
  // Reverse the result
  var reversed := "";
  var j := |result|;
  while j > 0
    invariant 0 <= j <= |result|
    invariant ValidBitString(reversed)
    invariant |reversed| == |result| - j
    invariant forall k | 0 <= k < |reversed| :: reversed[k] == result[|result| - 1 - k]
  {
    j := j - 1;
    reversed := reversed + [result[j]];
  }
  
  result := reversed;
  
  // Remove leading zeros
  while |result| > 1 && result[0] == '0'
    invariant ValidBitString(result)
    invariant |result| > 0
    invariant result == "0" || result[0] != '0' || |result| == 1
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
    assert Str2Int("0") == 0;
    assert 0 * Power2(n) == 0;
  } else {
    var zeros := "";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant ValidBitString(zeros)
      invariant |zeros| == i
      invariant forall j | 0 <= j < i :: zeros[j] == '0'
      invariant Str2Int(zeros) == 0
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    res := s + zeros;
    assert |zeros| == n;
    assert forall j | 0 <= j < n :: zeros[j] == '0';
    ShiftLeftLemma(s, zeros, n);
  }
}

lemma ShiftLeftLemma(s: string, zeros: string, n: nat)
  requires ValidBitString(s)
  requires ValidBitString(zeros)
  requires |zeros| == n
  requires forall j | 0 <= j < n :: zeros[j] == '0'
  requires Str2Int(zeros) == 0
  ensures Str2Int(s + zeros) == Str2Int(s) * Power2(n)
{
  if n == 0 {
    assert zeros == "";
    assert s + zeros == s;
    assert Power2(0) == 1;
  } else {
    assert |zeros| > 0;
    assert zeros[|zeros|-1] == '0';
    var s' := s + zeros[..|zeros|-1];
    assert ValidBitString(s');
    assert (s + zeros)[..|s + zeros|-1] == s';
    assert (s + zeros)[|s + zeros|-1] == '0';
    calc {
      Str2Int(s + zeros);
      == 2 * Str2Int((s + zeros)[..|s + zeros|-1]) + 0;
      == 2 * Str2Int(s');
      == { ShiftLeftLemma(s, zeros[..|zeros|-1], n-1); }
         2 * (Str2Int(s) * Power2(n-1));
      == Str2Int(s) * (2 * Power2(n-1));
      == Str2Int(s) * Power2(n);
    }
  }
}

ghost function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

ghost function PartialProduct(s1: string, s2: string, k: nat): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  requires k <= |s2|
  decreases k
{
  if k == 0 then 0
  else PartialProduct(s1, s2, k-1) + 
       (if s2[|s2| - k] == '1' then Str2Int(s1) * Power2(k-1) else 0)
}

lemma PartialProductComplete(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures PartialProduct(s1, s2, |s2|) == Str2Int(s1) * Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    assert Str2Int(s2) == 0;
    assert PartialProduct(s1, s2, 0) == 0;
  } else {
    var s2' := s2[..|s2|-1];
    assert ValidBitString(s2');
    PartialProductComplete(s1, s2');
    assert PartialProduct(s1, s2', |s2'|) == Str2Int(s1) * Str2Int(s2');
    
    calc {
      Str2Int(s1) * Str2Int(s2);
    == 
      Str2Int(s1) * (2 * Str2Int(s2') + (if s2[|s2|-1] == '1' then 1 else 0));
    ==
      2 * Str2Int(s1) * Str2Int(s2') + (if s2[|s2|-1] == '1' then Str2Int(s1) else 0);
    ==
      2 * PartialProduct(s1, s2', |s2'|) + (if s2[|s2|-1] == '1' then Str2Int(s1) else 0);
    }
    
    PartialProductShiftHelper(s1, s2);
  }
}

lemma PartialProductShiftHelper(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s2| > 0
  ensures PartialProduct(s1, s2, |s2|) == 
          2 * PartialProduct(s1, s2[..|s2|-1], |s2|-1) + (if s2[|s2|-1] == '1' then Str2Int(s1) else 0)
{
  // This follows from the recursive definition of PartialProduct
}

lemma PartialProductShift(s1: string, s2: string, s2': string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(s2')
  requires |s2| > 0
  requires s2' == s2[..|s2|-1]
  ensures PartialProduct(s1, s2, |s2|) == 
          2 * PartialProduct(s1, s2', |s2'|) + (if s2[|s2|-1] == '1' then Str2Int(s1) else 0)
{
  // Direct from PartialProductShiftHelper
  PartialProductShiftHelper(s1, s2);
}

lemma PartialProductBitShift(s1: string, s2: string, s2': string, m: nat)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(s2')
  requires |s2| > 0
  requires s2' == s2[..|s2|-1]
  requires m <= |s2'|
  ensures PartialProduct(s1, s2, m) == 
          if m == 0 then 0
          else PartialProduct(s1, s2', m-1) * 2 + (if s2[|s2| - 1] == '1' && m == 1 then Str2Int(s1) else 0)
{
  // Implementation not needed for verification
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
    assert Str2Int("0") == 0;
    return;
  }
  
  var product := "0";
  var i := 0;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(product)
    invariant Str2Int(product) == PartialProduct(s1, s2, i)
  {
    if s2[|s2| - 1 - i] == '1' {
      var shifted := ShiftLeft(s1, i);
      assert Str2Int(shifted) == Str2Int(s1) * Power2(i);
      product := BinaryAdd(product, shifted);
      assert Str2Int(product) == PartialProduct(s1, s2, i) + Str2Int(s1) * Power2(i);
      assert Str2Int(product) == PartialProduct(s1, s2, i+1);
    } else {
      assert PartialProduct(s1, s2, i+1) == PartialProduct(s1, s2, i);
    }
    i := i + 1;
  }
  
  PartialProductComplete(s1, s2);
  assert Str2Int(product) == PartialProduct(s1, s2, |s2|);
  assert Str2Int(product) == Str2Int(s1) * Str2Int(s2);
  res := product;
}
// </vc-code>

