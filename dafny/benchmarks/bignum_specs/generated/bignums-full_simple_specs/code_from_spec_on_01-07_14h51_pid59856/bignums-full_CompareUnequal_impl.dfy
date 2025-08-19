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
  /* code modified by LLM (iteration 1): Added lemma call to prove that longer strings without leading zeros represent larger numbers */
  LemmaLongerStringIsLarger(s1, s2);
  res := 1;
}

/* code modified by LLM (iteration 1): Added helper lemma to prove that a longer bit string represents a larger number */
lemma LemmaLongerStringIsLarger(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| > 0 && |s2| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
  ensures Str2Int(s1) > Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Use bounds on string values based on length */
  LemmaMinValueForLength(s1);
  LemmaMaxValueForLength(s2);
  
  /* code modified by LLM (iteration 1): Since |s1| > |s2| and both represent valid bit strings without leading zeros, s1 represents a larger number */
  if |s1| == 1 {
    /* code modified by LLM (iteration 1): If |s1| == 1 and |s1| > |s2|, then |s2| == 0, which contradicts |s2| > 0 */
    assert false;
  } else {
    /* code modified by LLM (iteration 1): s1 has length > 1, so s1[0] != '0', thus s1[0] == '1' */
    assert s1[0] == '1';
    
    /* code modified by LLM (iteration 1): Use the fact that s1 starts with '1' to get lower bound */
    LemmaPow2Growth(|s2|, |s1| - 1);
  }
}

/* code modified by LLM (iteration 1): Fixed lemma for minimum value of valid bit strings */
lemma LemmaMinValueForLength(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires |s| > 1 ==> s[0] != '0'
  ensures |s| == 1 ==> Str2Int(s) >= 0
  ensures |s| > 1 ==> Str2Int(s) >= Pow2(|s| - 1)
{
  if |s| == 1 {
    /* code modified by LLM (iteration 1): For single character, the value is either 0 or 1, both >= 0 */
  } else {
    assert s[0] != '0';
    assert s[0] == '1';
    LemmaStr2IntStructure(s);
  }
}

/* code modified by LLM (iteration 1): Added lemma for maximum value of bit strings */
lemma LemmaMaxValueForLength(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) < Pow2(|s|)
{
  if |s| == 1 {
    /* code modified by LLM (iteration 1): Single bit is at most 1, and Pow2(1) = 2 */
    assert Str2Int(s) <= 1;
    reveal Pow2;
    assert Pow2(1) == 2;
  } else {
    var prefix := s[0..|s|-1];
    LemmaMaxValueForLength(prefix);
    
    /* code modified by LLM (iteration 1): Use the recursive structure of Str2Int */
    calc {
      Str2Int(s);
      2 * Str2Int(prefix) + (if s[|s|-1] == '1' then 1 else 0);
      <= 2 * Str2Int(prefix) + 1;
      < 2 * Pow2(|prefix|) + 1; // by inductive hypothesis
      <= 2 * Pow2(|prefix|) + Pow2(|prefix|); // since 1 <= Pow2(|prefix|) when |prefix| >= 0
      == 3 * Pow2(|prefix|);
    }
    
    /* code modified by LLM (iteration 1): Actually, we need a tighter bound */
    if s[|s|-1] == '1' {
      assert Str2Int(s) == 2 * Str2Int(prefix) + 1;
      assert Str2Int(s) <= 2 * (Pow2(|prefix|) - 1) + 1;
      calc {
        2 * (Pow2(|prefix|) - 1) + 1;
        2 * Pow2(|prefix|) - 2 + 1;
        2 * Pow2(|prefix|) - 1;
        < 2 * Pow2(|prefix|);
      }
      reveal Pow2;
      assert 2 * Pow2(|prefix|) == Pow2(|s|);
    } else {
      assert Str2Int(s) == 2 * Str2Int(prefix);
      assert Str2Int(s) < 2 * Pow2(|prefix|);
      reveal Pow2;
      assert 2 * Pow2(|prefix|) == Pow2(|s|);
    }
  }
}

/* code modified by LLM (iteration 1): Added lemma for power of 2 growth */
lemma LemmaPow2Growth(a: nat, b: nat)
  requires a <= b
  ensures Pow2(a) <= Pow2(b)
{
  reveal Pow2;
  if a == b {
    // trivial
  } else {
    LemmaPow2Growth(a, b - 1);
  }
}

/* code modified by LLM (iteration 1): Simplified lemma for Str2Int structure with first bit being '1' */
lemma LemmaStr2IntStructure(s: string)
  requires ValidBitString(s)
  requires |s| >= 1
  requires s[0] == '1'
  ensures Str2Int(s) >= Pow2(|s| - 1)
{
  reveal Pow2;
  if |s| == 1 {
    assert Str2Int(s) == 1;
    assert Pow2(0) == 1;
  } else {
    var prefix := s[0..|s|-1];
    var lastBit := s[|s|-1];
    
    /* code modified by LLM (iteration 1): Since prefix starts with s[0] == '1' and has length >= 1 */
    assert prefix[0] == s[0] == '1';
    assert |prefix| >= 1;
    
    if |prefix| == 1 {
      assert Str2Int(prefix) == 1;
      assert Str2Int(s) >= 2 * 1 == 2;
      assert Pow2(|s| - 1) == Pow2(1) == 2;
    } else {
      LemmaStr2IntStructure(prefix);
      assert Str2Int(prefix) >= Pow2(|prefix| - 1);
      assert Str2Int(s) >= 2 * Pow2(|prefix| - 1);
      assert |prefix| == |s| - 1;
      assert 2 * Pow2(|s| - 2) == Pow2(|s| - 1);
    }
  }
}