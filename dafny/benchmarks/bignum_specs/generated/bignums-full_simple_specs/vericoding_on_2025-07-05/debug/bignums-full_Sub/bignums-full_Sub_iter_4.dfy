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

// Theo note: To check that Add/Sub/Mul only use Int2Str and Str2Int for verification:
// 1. Change Int2Str, OStr2Int, and Str2Int to `ghost function`
// 2. Delete Main (because it uses Int2Str/Str2Int in executable code, so now won't verify)
// 3. The rest of the code will still verify

// This function will be useful in proofs
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

//ATOM

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
    t := "";
    assume ValidBitString(t);
    assume |t| > 0;
    assume |t| > 1 ==> t[0] != '0';
    assume ValidBitString(s) ==> Str2Int(s) == Str2Int(t);
    return t;
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

//IMPL Sub
// ----------------------------------------------------
// string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Handle empty string cases properly */
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  
  if |s2| == 0 {
    res := if |s1| == 0 then "0" else s1;
    return;
  }
  
  if |s1| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Pad strings to same length */
  var len := if |s1| > |s2| then |s1| else |s2|;
  var a := s1;
  var b := s2;
  
  /* code modified by LLM (iteration 1): Add helper lemma for string concatenation validity */
  ghost var original_a := a;
  ghost var original_b := b;
  
  while |a| < len
    invariant ValidBitString(a)
    invariant |a| <= len
    decreases len - |a|
  {
    a := "0" + a;
    /* code modified by LLM (iteration 1): Assert validity after concatenation */
    assert ValidBitString("0");
    assert ValidBitString(a[1..]);
    assert ValidBitString(a);
  }
  
  while |b| < len
    invariant ValidBitString(b)
    invariant |b| <= len
    decreases len - |b|
  {
    b := "0" + b;
    /* code modified by LLM (iteration 1): Assert validity after concatenation */
    assert ValidBitString("0");
    assert ValidBitString(b[1..]);
    assert ValidBitString(b);
  }
  
  /* code modified by LLM (iteration 1): Implement subtraction with borrowing */
  var result := "";
  var borrow := 0;
  var i := len;
  
  while i > 0
    invariant 0 <= i <= len
    invariant ValidBitString(result)
    invariant 0 <= borrow <= 1
    invariant |a| == len && |b| == len
    invariant ValidBitString(a) && ValidBitString(b)
    decreases i
  {
    i := i - 1;
    var digit1 := if a[i] == '1' then 1 else 0;
    var digit2 := if b[i] == '1' then 1 else 0;
    
    var temp := digit1 - digit2 - borrow;
    
    if temp >= 0 {
      var new_digit := if temp == 1 then '1' else '0';
      result := [new_digit] + result;
      borrow := 0;
    } else {
      // temp is negative, need to borrow (add 2)
      var new_digit := if temp + 2 == 1 then '1' else '0';
      result := [new_digit] + result;
      borrow := 1;
    }
    
    /* code modified by LLM (iteration 1): Assert result validity */
    assert ValidBitString(result);
  }
  
  /* code modified by LLM (iteration 1): Normalize result by removing leading zeros */
  var normalized := result;
  while |normalized| > 1 && normalized[0] == '0'
    invariant |normalized| >= 1
    invariant ValidBitString(normalized)
    decreases |normalized|
  {
    normalized := normalized[1..];
    /* code modified by LLM (iteration 1): Assert validity after slicing */
    assert ValidBitString(normalized);
  }
  
  /* code modified by LLM (iteration 1): Ensure we always return a valid bit string */
  if |normalized| == 0 {
    normalized := "0";
  }
  
  res := normalized;
  /* code modified by LLM (iteration 1): Final validity assertion */
  assert ValidBitString(res);
}