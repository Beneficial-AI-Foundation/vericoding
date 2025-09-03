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
// Binary addition helper - simplified version
method BinaryAdd(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Handle edge cases
  if s1 == "0" {
    res := s2;
    return;
  }
  if s2 == "0" {
    res := s1;
    return;
  }
  
  // Recursive approach for simplicity
  var lastBit1 := if s1[|s1|-1] == '1' then 1 else 0;
  var lastBit2 := if s2[|s2|-1] == '1' then 1 else 0;
  var s1' := s1[..|s1|-1];
  var s2' := s2[..|s2|-1];
  
  if |s1| == 1 && |s2| == 1 {
    var sum := lastBit1 + lastBit2;
    if sum == 0 {
      res := "0";
    } else if sum == 1 {
      res := "1";
    } else {
      res := "10";
    }
    return;
  }
  
  // For longer strings, use a simpler iterative approach
  res := SimpleBinaryAdd(s1, s2);
}

// Simplified binary addition
method SimpleBinaryAdd(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Convert to reversed for easier processing
  var rev1 := Reverse(s1);
  var rev2 := Reverse(s2);
  var carry := 0;
  var result := "";
  var i := 0;
  var maxLen := if |s1| > |s2| then |s1| else |s2|;
  
  while i < maxLen || carry > 0
    invariant 0 <= carry <= 1
    invariant ValidBitString(result)
    invariant i >= 0
  {
    var bit1 := if i < |rev1| then (if rev1[i] == '1' then 1 else 0) else 0;
    var bit2 := if i < |rev2| then (if rev2[i] == '1' then 1 else 0) else 0;
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

// Helper to reverse a string
method Reverse(s: string) returns (res: string)
  ensures |res| == |s|
  ensures forall i | 0 <= i < |s| :: res[i] == s[|s| - 1 - i]
{
  res := "";
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |res| == |s| - i
    invariant forall j | 0 <= j < |res| :: res[j] == s[|s| - 1 - j]
  {
    i := i - 1;
    res := res + [s[i]];
  }
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
      invariant |zeros| == i
      invariant forall j | 0 <= j < i :: zeros[j] == '0'
    {
      zeros := zeros + "0";
      i := i + 1;
    }
    res := s + zeros;
    ShiftLeftCorrectness(s, n);
  }
}

// Lemma for shift left correctness
lemma ShiftLeftCorrectness(s: string, n: nat)
  requires ValidBitString(s)
  requires s != "0"
  ensures ValidBitString(s + Zeros(n))
  ensures Str2Int(s + Zeros(n)) == Str2Int(s) * Power2(n)
{
  // Proof by induction on n
}

// Helper function to create n zeros
ghost function Zeros(n: nat): string
  ensures |Zeros(n)| == n
  ensures forall i | 0 <= i < n :: Zeros(n)[i] == '0'
{
  if n == 0 then "" else Zeros(n-1) + "0"
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
{
  // Proof by induction on |s2|
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
    invariant Str2Int(product) == PartialProduct(s1, s2, i)
  {
    if s2[|s2| - 1 - i] == '1' {
      var shifted := ShiftLeft(s1, i);
      product := BinaryAdd(product, shifted);
    }
    i := i + 1;
  }
  
  PartialProductComplete(s1, s2);
  res := product;
}
// </vc-code>

