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
    if |s| == 0 {
        t := "0";
        return;
    }
    
    // Find first non-zero character
    var start := 0;
    while start < |s| && s[start] == '0'
        invariant 0 <= start <= |s|
        decreases |s| - start
    {
        start := start + 1;
    }
    
    // If all zeros, return "0"
    if start == |s| {
        t := "0";
        return;
    }
    
    // Extract substring from first non-zero character
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
  /* code modified by LLM (iteration 1): Handle edge cases properly */
  // Handle special cases
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  if |s1| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Use normalization correctly */
  var norm1 := NormalizeBitString(s1);
  var norm2 := NormalizeBitString(s2);
  
  if norm2 == "0" {
    res := norm1;
    return;
  }
  
  if norm1 == norm2 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Pad strings to same length with proper invariants */
  var a := norm1;
  var b := norm2;
  
  // Pad shorter string with leading zeros
  while |a| < |b|
    invariant ValidBitString(a) && ValidBitString(b)
    invariant Str2Int(a) == Str2Int(norm1)
    invariant Str2Int(b) == Str2Int(norm2)
    decreases |b| - |a|
  {
    a := "0" + a;
  }
  while |b| < |a|
    invariant ValidBitString(a) && ValidBitString(b)
    invariant Str2Int(a) == Str2Int(norm1)
    invariant Str2Int(b) == Str2Int(norm2)
    decreases |a| - |b|
  {
    b := "0" + b;
  }
  
  /* code modified by LLM (iteration 1): Perform binary subtraction with corrected string operations */
  var result := new char[|a|];
  var borrow := 0;
  var i := |a| - 1;
  
  while i >= 0
    invariant -1 <= i < |a|
    invariant |a| == |b|
    invariant ValidBitString(a) && ValidBitString(b)
    invariant 0 <= borrow <= 1
    invariant Str2Int(a) == Str2Int(norm1)  
    invariant Str2Int(b) == Str2Int(norm2)
    invariant result.Length == |a|
    invariant forall j | i < j < |a| :: result[j] == '0' || result[j] == '1'
    decreases i + 1
  {
    var digitA := if a[i] == '1' then 1 else 0;
    var digitB := if b[i] == '1' then 1 else 0;
    
    var diff := digitA - digitB - borrow;
    
    if diff >= 0 {
      result[i] := if diff == 1 then '1' else '0';
      borrow := 0;
    } else {
      // diff is -1 or -2, add 2 to handle borrow
      result[i] := if diff + 2 == 1 then '1' else '0';
      borrow := 1;
    }
    
    i := i - 1;
  }
  
  /* code modified by LLM (iteration 1): Convert array to string and normalize */
  var resultStr := "";
  var j := 0;
  while j < result.Length
    invariant 0 <= j <= result.Length
    invariant ValidBitString(resultStr)
    invariant |resultStr| == j
    decreases result.Length - j
  {
    resultStr := resultStr + [result[j]];
    j := j + 1;
  }
  
  /* code modified by LLM (iteration 1): Remove leading zeros */
  var start := 0;
  while start < |resultStr| && resultStr[start] == '0'
    invariant 0 <= start <= |resultStr|
    invariant ValidBitString(resultStr)
    decreases |resultStr| - start
  {
    start := start + 1;
  }
  
  if start == |resultStr| {
    res := "0";
  } else {
    res := resultStr[start..];
  }
}