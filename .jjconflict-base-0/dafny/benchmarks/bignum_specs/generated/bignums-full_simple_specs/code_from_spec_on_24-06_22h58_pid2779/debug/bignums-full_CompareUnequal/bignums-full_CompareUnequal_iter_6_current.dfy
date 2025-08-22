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


//IMPL CompareUnequal

/* code modified by LLM (iteration 1): Simple power of 2 function */
function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

/* code modified by LLM (iteration 1): Power inequality lemma */
lemma PowerInequality(a: nat, b: nat)
  requires a <= b
  ensures Power2(a) <= Power2(b)
{
  if a == b {
    // trivial
  } else if a < b {
    PowerInequality(a, b - 1);
    assert Power2(a) <= Power2(b - 1);
    assert Power2(b) == 2 * Power2(b - 1);
  }
}

/* code modified by LLM (iteration 1): Maximum value lemma */
lemma StringMaxValue(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) < Power2(|s|)
{
  if |s| == 1 {
    if s == "0" {
      assert Str2Int(s) == 0;
      assert Power2(1) == 2;
    } else {
      assert s == "1";
      assert Str2Int(s) == 1;
      assert Power2(1) == 2;
    }
  } else {
    var prefix := s[0..|s|-1];
    var lastBit := s[|s|-1];
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if lastBit == '1' then 1 else 0);
    StringMaxValue(prefix);
    assert Str2Int(prefix) < Power2(|s| - 1);
    assert Power2(|s|) == 2 * Power2(|s| - 1);
    if lastBit == '1' {
      assert Str2Int(s) == 2 * Str2Int(prefix) + 1;
      assert Str2Int(s) < 2 * Power2(|s| - 1) + 1;
      assert Str2Int(s) < Power2(|s|);
    } else {
      assert Str2Int(s) == 2 * Str2Int(prefix);
      assert Str2Int(s) < 2 * Power2(|s| - 1);
      assert Str2Int(s) < Power2(|s|);
    }
  }
}

/* code modified by LLM (iteration 1): Minimum value lemma for normalized strings */
lemma StringMinValue(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires |s| > 1 ==> s[0] == '1'
  ensures |s| == 1 && s == "0" ==> Str2Int(s) == 0
  ensures |s| == 1 && s == "1" ==> Str2Int(s) >= Power2(|s| - 1)
  ensures |s| > 1 ==> Str2Int(s) >= Power2(|s| - 1)
{
  if |s| == 1 {
    if s == "1" {
      assert Str2Int(s) == 1;
      assert Power2(0) == 1;
    } else {
      assert s == "0";
      assert Str2Int(s) == 0;
    }
  } else {
    assert s[0] == '1';
    var prefix := s[0..|s|-1];
    var lastBit := s[|s|-1];
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if lastBit == '1' then 1 else 0);
    
    if |prefix| > 1 {
      StringMinValue(prefix);
      assert Str2Int(prefix) >= Power2(|prefix| - 1);
    } else {
      assert prefix == "1";
      assert Str2Int(prefix) == 1;
      assert Power2(0) == 1;
    }
    
    assert Str2Int(s) >= 2 * Power2(|prefix| - 1);
    assert |prefix| == |s| - 1;
    assert Str2Int(s) >= 2 * Power2(|s| - 2);
    assert Power2(|s| - 1) == 2 * Power2(|s| - 2);
    assert Str2Int(s) >= Power2(|s| - 1);
  }
}

/* code modified by LLM (iteration 1): Helper lemma to establish that longer normalized strings represent larger numbers */
lemma LongerStringIsGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] == '1'
  requires |s2| > 1 ==> s2[0] == '1'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  if s2 == "0" {
    assert Str2Int(s2) == 0;
    if s1 == "1" {
      assert Str2Int(s1) == 1;
    } else {
      StringMinValue(s1);
      assert Str2Int(s1) >= Power2(|s1| - 1);
      assert Power2(|s1| - 1) >= 1;
    }
  } else {
    StringMinValue(s1);
    StringMaxValue(s2);
    PowerInequality(|s2|, |s1| - 1);
    
    if |s1| > 1 {
      assert Str2Int(s1) >= Power2(|s1| - 1);
    } else {
      assert s1 == "1";
      assert Str2Int(s1) == 1;
    }
    
    assert Str2Int(s2) < Power2(|s2|);
    assert Power2(|s2|) <= Power2(|s1| - 1);
    
    if |s1| > 1 {
      assert Str2Int(s2) < Power2(|s2|) <= Power2(|s1| - 1) <= Str2Int(s1);
    }
  }
}

/* code modified by LLM (iteration 1): Helper lemma for lexicographic comparison of equal length strings */
lemma SameLengthComparison(s1: string, s2: string, i: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && |s1| > 0
  requires i < |s1|
  requires s1[i] != s2[i]
  requires forall j | 0 <= j < i :: s1[j] == s2[j]
  ensures (s1[i] == '1' && s2[i] == '0') ==> Str2Int(s1) > Str2Int(s2)
  ensures (s1[i] == '0' && s2[i] == '1') ==> Str2Int(s1) < Str2Int(s2)
{
  var n := |s1|;
  var val1 := Str2Int(s1);
  var val2 := Str2Int(s2);
  
  // Split the strings into prefix, differing bit, and suffix
  var prefix := s1[0..i];
  var suffix1 := s1[i+1..n];
  var suffix2 := s2[i+1..n];
  var bit1 := s1[i];
  var bit2 := s2[i];
  
  // Since prefix is the same
  assert prefix == s2[0..i];
  var prefixVal := if i == 0 then 0 else Str2Int(prefix);
  
  // Express the values in terms of prefix, bit, and suffix
  var suffixVal1 := if i + 1 == n then 0 else Str2Int(suffix1);
  var suffixVal2 := if i + 1 == n then 0 else Str2Int(suffix2);
  
  var contribution1 := Power2(n - i - 1) * (if bit1 == '1' then 1 else 0);
  var contribution2 := Power2(n - i - 1) * (if bit2 == '1' then 1 else 0);
  
  if bit1 == '1' && bit2 == '0' {
    assert contribution1 == Power2(n - i - 1);
    assert contribution2 == 0;
    if i + 1 < n {
      StringMaxValue(suffix2);
      assert suffixVal2 < Power2(n - i - 1);
    } else {
      assert suffixVal2 == 0;
    }
    assert val1 - val2 >= Power2(n - i - 1) - suffixVal2 > 0;
  } else if bit1 == '0' && bit2 == '1' {
    assert contribution1 == 0;
    assert contribution2 == Power2(n - i - 1);
    if i + 1 < n {
      StringMaxValue(suffix1);
      assert suffixVal1 < Power2(n - i - 1);
    } else {
      assert suffixVal1 == 0;
    }
    assert val2 - val1 >= Power2(n - i - 1) - suffixVal1 > 0;
  }
}

/* code modified by LLM (iteration 1): Method to compare strings of equal length lexicographically */
method CompareSameLength(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2| && |s1| > 0
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
{
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant forall j | 0 <= j < i :: s1[j] == s2[j]
  {
    if s1[i] != s2[i] {
      if s1[i] == '1' && s2[i] == '0' {
        SameLengthComparison(s1, s2, i);
        return 1;
      } else {
        SameLengthComparison(s1, s2, i);
        return -1;
      }
    }
    i := i + 1;
  }
  // If we reach here, all characters are equal
  assert s1 == s2;
  assert Str2Int(s1) == Str2Int(s2);
  return 0;
}

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
  /* code modified by LLM (iteration 1): Given the precondition |s1| > |s2| and normalization constraints, s1 must be greater than s2 */
  LongerStringIsGreater(s1, s2);
  res := 1;
}