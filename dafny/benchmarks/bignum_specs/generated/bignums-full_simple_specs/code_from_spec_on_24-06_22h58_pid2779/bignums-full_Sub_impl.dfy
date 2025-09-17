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

// note: To check that Add/Sub/Mul only use Int2Str and Str2Int for verification:
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
  /* code modified by LLM (iteration 2): Handle empty string cases */
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

  /* code modified by LLM (iteration 2): Check if s2 represents zero */
  var s2_is_zero := true;
  var j := 0;
  while j < |s2|
    invariant 0 <= j <= |s2|
    invariant s2_is_zero <==> forall k | 0 <= k < j :: s2[k] == '0'
  {
    if s2[j] == '1' {
      s2_is_zero := false;
      break;
    }
    j := j + 1;
  }
  
  if s2_is_zero {
    res := s1;
    return;
  }

  /* code modified by LLM (iteration 2): Pad strings to same length */
  var a1 := s1;
  var a2 := s2;
  
  while |a1| < |a2|
    invariant ValidBitString(a1) && ValidBitString(a2)
    invariant Str2Int(a1) == Str2Int(s1)
    invariant Str2Int(a2) == Str2Int(s2)
    decreases |a2| - |a1|
  {
    a1 := "0" + a1;
  }
  
  while |a2| < |a1|
    invariant ValidBitString(a1) && ValidBitString(a2)
    invariant Str2Int(a1) == Str2Int(s1)
    invariant Str2Int(a2) == Str2Int(s2)
    decreases |a1| - |a2|
  {
    a2 := "0" + a2;
  }

  /* code modified by LLM (iteration 2): Implement binary subtraction with proper borrowing */
  var result := new char[|a1|];
  var borrow := 0;
  var i := |a1| - 1;
  
  while i >= 0
    invariant -1 <= i < |a1|
    invariant |a1| == |a2|
    invariant ValidBitString(a1) && ValidBitString(a2)
    invariant 0 <= borrow <= 1
    invariant Str2Int(a1) == Str2Int(s1)
    invariant Str2Int(a2) == Str2Int(s2)
    invariant forall k | i + 1 <= k < |a1| :: result[k] == '0' || result[k] == '1'
    decreases i + 1
  {
    var bit1 := if a1[i] == '1' then 1 else 0;
    var bit2 := if a2[i] == '1' then 1 else 0;
    
    var diff := bit1 - bit2 - borrow;
    
    /* code modified by LLM (iteration 2): Correct subtraction with borrowing */
    if diff >= 0 {
      result[i] := if diff == 1 then '1' else '0';
      borrow := 0;
    } else {
      // diff is negative, so we need to borrow
      result[i] := if diff + 2 == 1 then '1' else '0';
      borrow := 1;
    }
    
    i := i - 1;
  }
  
  /* code modified by LLM (iteration 2): Convert array to string */
  var result_str := "";
  var k := 0;
  while k < |a1|
    invariant 0 <= k <= |a1|
    invariant ValidBitString(result_str)
    invariant |result_str| == k
    invariant forall j | 0 <= j < k :: result_str[j] == result[j]
  {
    result_str := result_str + [result[k]];
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 2): Normalize result by removing leading zeros */
  var normalized := result_str;
  while |normalized| > 1 && normalized[0] == '0'
    invariant ValidBitString(normalized)
    invariant |normalized| >= 1
    invariant |normalized| <= |result_str|
    decreases |normalized|
  {
    normalized := normalized[1..];
  }
  
  /* code modified by LLM (iteration 2): Ensure we have at least one character */
  if |normalized| == 0 {
    normalized := "0";
  }
  
  res := normalized;
}