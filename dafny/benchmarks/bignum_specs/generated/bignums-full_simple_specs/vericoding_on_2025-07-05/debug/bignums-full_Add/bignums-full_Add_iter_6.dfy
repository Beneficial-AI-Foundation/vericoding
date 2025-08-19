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

//IMPL Add
// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Handle empty strings correctly */
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  if |s1| == 0 {
    res := if |s2| == 0 then "0" else s2;
    return;
  }
  if |s2| == 0 {
    res := s1;
    return;
  }

  /* code modified by LLM (iteration 1): Implement binary addition with proper verification */
  var result: seq<char> := [];
  var carry := 0;
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  /* code modified by LLM (iteration 1): Add helper ghost function for verification */
  ghost function BitValue(s: string, i: int): int
    requires ValidBitString(s)
    requires 0 <= i < |s|
  {
    if s[i] == '1' then 1 else 0
  }
  
  while i1 >= 0 || i2 >= 0 || carry > 0
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
    invariant 0 <= carry <= 1
    invariant ValidBitString(result)
    decreases (if i1 >= 0 then i1 + 1 else 0) + (if i2 >= 0 then i2 + 1 else 0) + carry
  {
    var bit1 := if i1 >= 0 && s1[i1] == '1' then 1 else 0;
    var bit2 := if i2 >= 0 && s2[i2] == '1' then 1 else 0;
    
    var sum := bit1 + bit2 + carry;
    
    var resultBit := if sum % 2 == 1 then '1' else '0';
    carry := sum / 2;
    
    result := [resultBit] + result;
    
    i1 := i1 - 1;
    i2 := i2 - 1;
  }
  
  /* code modified by LLM (iteration 1): Convert sequence to string and normalize */
  var resultStr := "";
  var k := 0;
  while k < |result|
    invariant 0 <= k <= |result|
    invariant ValidBitString(resultStr)
    invariant |resultStr| == k
  {
    resultStr := resultStr + [result[k]];
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Remove leading zeros properly */
  if |resultStr| == 0 {
    res := "0";
    return;
  }
  
  var start := 0;
  while start < |resultStr| - 1 && resultStr[start] == '0'
    invariant 0 <= start < |resultStr|
    decreases |resultStr| - start
  {
    start := start + 1;
  }
  
  res := resultStr[start..];
}