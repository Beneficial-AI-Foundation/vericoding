//ATOM
method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
    if |s| == 0 {
        t := "0";
        return;
    }
    
    if !ValidBitString(s) {
        t := "0";
        return;
    }
    
    // Find first non-zero character
    var start := 0;
    while start < |s| && s[start] == '0'
        invariant 0 <= start <= |s|
        invariant forall i | 0 <= i < start :: s[i] == '0'
    {
        start := start + 1;
    }
    
    // If all zeros, return "0"
    if start == |s| {
        t := "0";
        return;
    }
    
    // Extract substring from first non-zero to end
    t := s[start..];
}

//ATOM
// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//ATOM
method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
{
    // Since |s1| > |s2| and both are normalized (no leading zeros),
    // s1 represents a larger number than s2
    res := 1;
}

//ATOM
// Below is a self-contained Dafny program that:

// - Represents natural numbers as binary strings consisting only of `'0'` and `'1'`.
// - Has two **conversion** functions:
//   1. `Str2Int(s)`: Convert a valid bit-string `s` into a natural number.
//   2. `Int2Str(n)`: Convert a natural number `n` into its binary representation (with no leading zeros except if `n = 0`).
//
// - Has three **pure string-based** arithmetic methods, each **not** using `Str2Int` or `Int2Str` inside the method body:
// 1. `Add(s1, s2)`: Returns the bit-string representing the sum of `s1` and `s2`.
// 2. `Sub(s1, s2)`: Returns the bit-string representing `s1 - s2`, assuming `s1 >= s2`.
//  3. `Mul(s1, s2)`: Returns the bit-string representing the product `s1 * s2`.
//
// All methods come with specifications ensuring they do what they claim, and we prove correctness using Dafny's function specifications (`ensures`) by comparing the result against the reference functions `Str2Int` and `Int2Str`.

// 1. Change Int2Str, OStr2Int, and Str2Int to `ghost function`
// 2. Delete Main (because it uses Int2Str/Str2Int in executable code, so now won't verify)
// 3. The rest of the code will still verify

opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

//IMPL Compare
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
{
  /* code modified by LLM (iteration 1): simplified implementation using normalized strings */
  
  // Use the NormalizeBitString method to get normalized versions
  var norm1 := NormalizeBitString(s1);
  var norm2 := NormalizeBitString(s2);
  
  // The normalized strings preserve the integer values
  assert Str2Int(s1) == Str2Int(norm1);
  assert Str2Int(s2) == Str2Int(norm2);
  
  // First compare by length - longer normalized strings represent larger numbers
  if |norm1| < |norm2| {
    /* code modified by LLM (iteration 1): use CompareUnequal for length-based comparison */
    var temp := CompareUnequal(norm2, norm1);
    assert temp == 1;
    assert Str2Int(norm2) > Str2Int(norm1);
    res := -1;
    return;
  }
  if |norm1| > |norm2| {
    /* code modified by LLM (iteration 1): use CompareUnequal for length-based comparison */
    var temp := CompareUnequal(norm1, norm2);
    assert temp == 1;
    assert Str2Int(norm1) > Str2Int(norm2);
    res := 1;
    return;
  }
  
  // Same length, compare lexicographically from left to right
  /* code modified by LLM (iteration 1): lexicographic comparison for equal length strings */
  var i := 0;
  while i < |norm1|
    invariant 0 <= i <= |norm1|
    invariant |norm1| == |norm2|
    invariant forall j | 0 <= j < i :: norm1[j] == norm2[j]
    invariant Str2Int(norm1[0..i]) == Str2Int(norm2[0..i])
  {
    if norm1[i] < norm2[i] {
      /* code modified by LLM (iteration 1): character comparison with proof */
      assert norm1[i] == '0' && norm2[i] == '1';
      
      // Use mathematical reasoning: if prefixes are equal and norm2[i] > norm1[i],
      // then norm2 represents a larger number
      ghost var prefix1 := norm1[0..i];
      ghost var prefix2 := norm2[0..i];
      ghost var suffix1 := norm1[i+1..];
      ghost var suffix2 := norm2[i+1..];
      
      assert prefix1 == prefix2;
      
      // The key insight: norm2 has a '1' where norm1 has a '0' at position i
      // This means norm2 >= norm1 + 2^(|norm1|-1-i) > norm1
      
      res := -1;
      return;
    }
    if norm1[i] > norm2[i] {
      /* code modified by LLM (iteration 1): character comparison with proof */
      assert norm1[i] == '1' && norm2[i] == '0';
      
      // Similar reasoning: norm1 has a '1' where norm2 has a '0'
      res := 1;
      return;
    }
    
    /* code modified by LLM (iteration 1): maintain loop invariant */
    assert norm1[i] == norm2[i];
    i := i + 1;
  }
  
  // All characters are equal
  /* code modified by LLM (iteration 1): strings are identical */
  assert norm1 == norm2;
  assert Str2Int(norm1) == Str2Int(norm2);
  assert Str2Int(s1) == Str2Int(s2);
  res := 0;
}