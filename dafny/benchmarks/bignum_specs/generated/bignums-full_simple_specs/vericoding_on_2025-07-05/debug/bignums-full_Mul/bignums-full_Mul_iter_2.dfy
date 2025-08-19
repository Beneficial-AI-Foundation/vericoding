//ATOM


// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
    return res;
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


// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
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


//IMPL Mul

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  // Handle empty strings as zero
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  // Initialize result to zero
  res := "0";
  var multiplicand := s1;
  var i := |s2| - 1;
  /* code modified by LLM (iteration 1): Added power tracking variable and helper lemma for left shift */
  var power := 0;
  
  // Process each bit of s2 from right to left
  while i >= 0
    invariant -1 <= i < |s2|
    invariant ValidBitString(res)
    invariant ValidBitString(multiplicand)
    /* code modified by LLM (iteration 1): Added invariants to track mathematical relationship */
    invariant power == |s2| - 1 - i
    invariant power >= 0
    invariant Str2Int(multiplicand) == Str2Int(s1) * Pow2(power)
    invariant Str2Int(res) == Str2Int(s1) * PartialSum(s2, i + 1)
  {
    // If current bit of s2 is '1', add multiplicand to result
    if s2[i] == '1' {
      res := Add(res, multiplicand);
    }
    
    // Left shift multiplicand (multiply by 2) by appending '0'
    if i > 0 {
      multiplicand := multiplicand + "0";
      /* code modified by LLM (iteration 1): Added assertion to help verification */
      assert Str2Int(multiplicand) == Str2Int(s1) * Pow2(power + 1);
    }
    
    i := i - 1;
    power := power + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to connect loop invariant to postcondition */
  assert Str2Int(res) == Str2Int(s1) * PartialSum(s2, 0);
  assert PartialSum(s2, 0) == Str2Int(s2);
  
  // Normalize the result to remove leading zeros
  res := NormalizeBitString(res);
}

/* code modified by LLM (iteration 1): Added helper functions for mathematical reasoning */
function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function PartialSum(s: string, start: nat): nat
  requires ValidBitString(s)
  requires 0 <= start <= |s|
{
  if start >= |s| then 0
  else (if s[start] == '1' then Pow2(|s| - 1 - start) else 0) + PartialSum(s, start + 1)
}

/* code modified by LLM (iteration 1): Added lemma to connect PartialSum to Str2Int */
lemma PartialSumEqualsStr2Int(s: string)
  requires ValidBitString(s)
  ensures PartialSum(s, 0) == Str2Int(s)
{
  if |s| == 0 {
    assert PartialSum(s, 0) == 0;
    assert Str2Int(s) == 0;
  } else {
    PartialSumEqualsStr2IntHelper(s, 0);
  }
}

lemma PartialSumEqualsStr2IntHelper(s: string, start: nat)
  requires ValidBitString(s)
  requires 0 <= start <= |s|
  ensures PartialSum(s, start) == Str2IntFromIndex(s, start)
  decreases |s| - start
{
  if start >= |s| {
    assert PartialSum(s, start) == 0;
    assert Str2IntFromIndex(s, start) == 0;
  } else {
    PartialSumEqualsStr2IntHelper(s, start + 1);
  }
}

function Str2IntFromIndex(s: string, start: nat): nat
  requires ValidBitString(s)
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start >= |s| then 0
  else 2 * Str2IntFromIndex(s, start + 1) + (if s[start] == '1' then 1 else 0)
}