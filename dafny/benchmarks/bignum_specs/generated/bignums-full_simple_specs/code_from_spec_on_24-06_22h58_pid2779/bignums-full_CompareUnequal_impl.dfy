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

/* code modified by LLM (iteration 1): Power of 2 function */
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
    // Base case: equal powers
  } else {
    PowerInequality(a, b - 1);
  }
}

/* code modified by LLM (iteration 1): Maximum value lemma for bit strings */
lemma StringMaxValue(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) < Power2(|s|)
{
  if |s| == 1 {
    // Base case
  } else {
    var prefix := s[0..|s|-1];
    StringMaxValue(prefix);
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
    // Base cases for single character strings
  } else {
    var prefix := s[0..|s|-1];
    if |prefix| > 1 {
      StringMinValue(prefix);
    }
  }
}

/* code modified by LLM (iteration 1): Lemma showing longer normalized strings represent larger numbers */
lemma LongerStringIsGreater(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] == '1'
  requires |s2| > 1 ==> s2[0] == '1'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  if s2 == "0" {
    // s2 represents 0, any valid s1 with greater length represents at least 1
    if |s1| == 1 {
      assert s1 == "1";
    } else {
      StringMinValue(s1);
    }
  } else {
    // Both strings are normalized and s1 is longer
    StringMinValue(s1);
    StringMaxValue(s2);
    PowerInequality(|s2|, |s1| - 1);
    
    // s1 represents at least 2^(|s1|-1)
    // s2 represents less than 2^|s2|
    // Since |s1| > |s2|, we have 2^|s2| <= 2^(|s1|-1)
    // Therefore Str2Int(s2) < 2^|s2| <= 2^(|s1|-1) <= Str2Int(s1)
  }
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
  /* code modified by LLM (iteration 1): Apply lemma to prove s1 > s2 given the preconditions */
  LongerStringIsGreater(s1, s2);
  res := 1;
}