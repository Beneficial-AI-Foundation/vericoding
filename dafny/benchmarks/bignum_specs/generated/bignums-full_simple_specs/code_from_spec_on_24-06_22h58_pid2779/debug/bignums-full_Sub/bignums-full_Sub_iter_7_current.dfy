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
  /* code modified by LLM (iteration 4): Fixed base cases and empty string handling */
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  if |s2| == 0 {
    res := NormalizeBitString(s1);
    return;
  }
  if |s1| == 0 {
    res := "0"; 
    return;
  }

  /* code modified by LLM (iteration 4): Fixed padding with proper ValidBitString maintenance */
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

  /* code modified by LLM (iteration 4): Rewritten subtraction algorithm with correct syntax */
  var result := "";
  var borrow := 0;
  var i := |a1| - 1;
  
  while i >= 0
    invariant -1 <= i < |a1|
    invariant |a1| == |a2|
    invariant ValidBitString(a1) && ValidBitString(a2)
    invariant ValidBitString(result)
    invariant 0 <= borrow <= 1
    decreases i + 1
  {
    var bit1 := if a1[i] == '1' then 1 else 0;
    var bit2 := if a2[i] == '1' then 1 else 0;
    
    var temp := bit1 - bit2 - borrow;
    
    var resultBit: char;
    var newBorrow: int;
    
    if temp == 1 {
      resultBit := '1';
      newBorrow := 0;
    } else if temp == 0 {
      resultBit := '0';
      newBorrow := 0;
    } else if temp == -1 {
      resultBit := '1';
      newBorrow := 1;
    } else { // temp == -2
      resultBit := '0';
      newBorrow := 1;
    }
    
    borrow := newBorrow;
    
    /* code modified by LLM (iteration 4): Fixed string concatenation syntax */
    var charAsString: string := [resultBit];
    result := charAsString + result;
    i := i - 1;
  }
  
  /* code modified by LLM (iteration 4): Use NormalizeBitString to handle result */
  res := NormalizeBitString(result);
}