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

/* code modified by LLM (iteration 1): added helper lemma for normalized string length comparison */
lemma LengthImpliesValue(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  // For normalized strings, longer length means larger value
  if |s2| == 1 {
    assert s2 == "0" || s2 == "1";
    assert Str2Int(s2) <= 1;
    assert |s1| >= 2;
    LengthLowerBound(s1);
    assert Str2Int(s1) >= 2;
  } else {
    LengthLowerBound(s1);
    LengthUpperBound(s2);
  }
}

/* code modified by LLM (iteration 1): added helper lemma for lower bound based on length */
lemma LengthLowerBound(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires |s| > 1 ==> s[0] != '0'
  ensures Str2Int(s) >= Pow2(|s| - 1)
  decreases |s|
{
  if |s| == 1 {
    assert Str2Int(s) >= 0;
    reveal Pow2();
  } else {
    assert s[0] == '1';
    var rest := s[1..];
    assert ValidBitString(rest);
    assert Str2Int(s) == 2 * Str2Int(rest) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) >= 2 * Str2Int(rest);
    reveal Pow2();
  }
}

/* code modified by LLM (iteration 1): added helper lemma for upper bound based on length */
lemma LengthUpperBound(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) < Pow2(|s|)
  decreases |s|
{
  if |s| == 1 {
    reveal Pow2();
  } else {
    var rest := s[0..|s|-1];
    assert ValidBitString(rest);
    LengthUpperBound(rest);
    reveal Pow2();
  }
}

/* code modified by LLM (iteration 1): added helper lemma for lexicographic comparison */
lemma LexicographicComparison(s1: string, s2: string, pos: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| > 0
  requires 0 <= pos < |s1|
  requires forall j | 0 <= j < pos :: s1[j] == s2[j]
  requires s1[pos] > s2[pos]
  ensures Str2Int(s1) > Str2Int(s2)
  decreases |s1| - pos
{
  if pos == |s1| - 1 {
    // Last character differs
    var prefix1 := s1[0..|s1|-1];
    var prefix2 := s2[0..|s2|-1];
    assert prefix1 == prefix2;
    assert Str2Int(prefix1) == Str2Int(prefix2);
    assert s1[|s1|-1] == '1' && s2[|s2|-1] == '0';
  } else {
    // Recursive case
    var suffix1 := s1[pos+1..];
    var suffix2 := s2[pos+1..];
    var bit1 := if s1[pos] == '1' then 1 else 0;
    var bit2 := if s2[pos] == '1' then 1 else 0;
    assert bit1 > bit2;
    
    reveal Pow2();
    LengthUpperBound(suffix1);
    LengthUpperBound(suffix2);
  }
}

//IMPL Compare
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
{
  /* code modified by LLM (iteration 1): implemented proper bit string comparison using normalized strings */
  
  // Use the NormalizeBitString method to get normalized versions
  var norm1 := NormalizeBitString(s1);
  var norm2 := NormalizeBitString(s2);
  
  // First compare by length - longer normalized strings represent larger numbers
  if |norm1| < |norm2| {
    /* code modified by LLM (iteration 1): direct comparison for different lengths with proof */
    LengthImpliesValue(norm2, norm1);
    res := -1;
    return;
  }
  if |norm1| > |norm2| {
    /* code modified by LLM (iteration 1): direct comparison for different lengths with proof */
    LengthImpliesValue(norm1, norm2);
    res := 1;
    return;
  }
  
  // Same length, compare lexicographically from left to right
  /* code modified by LLM (iteration 1): lexicographic comparison for same-length normalized strings */
  var i := 0;
  while i < |norm1|
    invariant 0 <= i <= |norm1|
    invariant |norm1| == |norm2|
    invariant forall j | 0 <= j < i :: norm1[j] == norm2[j]
  {
    if norm1[i] < norm2[i] {
      /* code modified by LLM (iteration 1): added proof for lexicographic less-than case */
      LexicographicComparison(norm2, norm1, i);
      res := -1;
      return;
    }
    if norm1[i] > norm2[i] {
      /* code modified by LLM (iteration 1): added proof for lexicographic greater-than case */
      LexicographicComparison(norm1, norm2, i);
      res := 1;
      return;
    }
    i := i + 1;
  }
  
  // All characters are equal
  /* code modified by LLM (iteration 1): strings are identical, so values are equal */
  assert norm1 == norm2;
  assert Str2Int(norm1) == Str2Int(norm2);
  assert Str2Int(s1) == Str2Int(norm1) == Str2Int(norm2) == Str2Int(s2);
  res := 0;
}