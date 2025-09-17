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

//IMPL Add
// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  
  if |s1| == 0 {
    res := s2;
    return;
  }
  
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  // Pad strings to same length
  var len := if |s1| > |s2| then |s1| else |s2|
  var str1 := "";
  var str2 := "";
  
  // Pad s1
  var i := 0;
  while i < len - |s1| {
    str1 := str1 + "0";
    i := i + 1;
  }
  str1 := str1 + s1;
  
  // Pad s2
  i := 0;
  while i < len - |s2| {
    str2 := str2 + "0";
    i := i + 1;
  }
  str2 := str2 + s2;
  
  // Perform addition from right to left
  var result := "";
  var carry := '0';
  i := len - 1;
  
  while i >= 0 {
    var bit1 := str1[i];
    var bit2 := str2[i];
    
    if bit1 == '0' && bit2 == '0' && carry == '0' {
      result := "0" + result;
      carry := '0';
    } else if (bit1 == '0' && bit2 == '0' && carry == '1') ||
              (bit1 == '0' && bit2 == '1' && carry == '0') ||
              (bit1 == '1' && bit2 == '0' && carry == '0') {
      result := "1" + result;
      carry := '0';
    } else if (bit1 == '0' && bit2 == '1' && carry == '1') ||
              (bit1 == '1' && bit2 == '0' && carry == '1') ||
              (bit1 == '1' && bit2 == '1' && carry == '0') {
      result := "0" + result;
      carry := '1';
    } else { // bit1 == '1' && bit2 == '1' && carry == '1'
      result := "1" + result;
      carry := '1';
    }
    
    i := i - 1;
  }
  
  if carry == '1' {
    result := "1" + result;
  }
  
  // Normalize result (remove leading zeros)
  var normalized := NormalizeBitString(result);
  res := normalized;
}