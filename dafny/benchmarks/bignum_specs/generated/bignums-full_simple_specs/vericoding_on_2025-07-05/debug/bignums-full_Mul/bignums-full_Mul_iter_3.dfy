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
  var i := |s2| - 1;
  /* code modified by LLM (iteration 1): Simplified approach using shift count */
  var shift_count := 0;
  
  // Process each bit of s2 from right to left
  while i >= 0
    invariant -1 <= i < |s2|
    invariant ValidBitString(res)
    invariant shift_count == |s2| - 1 - i
    invariant shift_count >= 0
    /* code modified by LLM (iteration 1): Simplified invariant using mathematical properties */
    invariant Str2Int(res) == Str2Int(s1) * RightBitsValue(s2, i + 1)
  {
    // If current bit of s2 is '1', add s1 shifted left by shift_count positions
    if s2[i] == '1' {
      /* code modified by LLM (iteration 1): Create shifted version of s1 */
      var shifted_s1 := LeftShift(s1, shift_count);
      res := Add(res, shifted_s1);
    }
    
    i := i - 1;
    shift_count := shift_count + 1;
  }
  
  /* code modified by LLM (iteration 1): Final assertion to connect to postcondition */
  RightBitsValueComplete(s2);
  assert RightBitsValue(s2, 0) == Str2Int(s2);
  
  // Normalize the result to remove leading zeros
  res := NormalizeBitString(res);
}

/* code modified by LLM (iteration 1): Helper function to create left-shifted string */
function LeftShift(s: string, n: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(LeftShift(s, n))
  ensures Str2Int(LeftShift(s, n)) == Str2Int(s) * Pow2(n)
{
  if n == 0 then s else s + ZeroString(n)
}

/* code modified by LLM (iteration 1): Helper function to create string of zeros */
function ZeroString(n: nat): string
  ensures ValidBitString(ZeroString(n))
  ensures |ZeroString(n)| == n
  ensures Str2Int(ZeroString(n)) == 0
{
  if n == 0 then "" else ZeroString(n - 1) + "0"
}

/* code modified by LLM (iteration 1): Helper function for power of 2 */
function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

/* code modified by LLM (iteration 1): Function to compute value of rightmost bits */
function RightBitsValue(s: string, start: nat): nat
  requires ValidBitString(s)
  requires 0 <= start <= |s|
{
  if start >= |s| then 0
  else (if s[start] == '1' then Pow2(|s| - 1 - start) else 0) + RightBitsValue(s, start + 1)
}

/* code modified by LLM (iteration 1): Lemma to prove RightBitsValue equals Str2Int for complete string */
lemma RightBitsValueComplete(s: string)
  requires ValidBitString(s)
  ensures RightBitsValue(s, 0) == Str2Int(s)
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    var s_prefix := s[0..|s|-1];
    var last_bit := s[|s|-1];
    
    assert s == s_prefix + [last_bit];
    assert ValidBitString(s_prefix);
    
    RightBitsValueComplete(s_prefix);
    RightBitsValueRecursive(s, 0);
  }
}

/* code modified by LLM (iteration 1): Helper lemma for recursive structure */
lemma RightBitsValueRecursive(s: string, start: nat)
  requires ValidBitString(s)
  requires 0 <= start < |s|
  ensures RightBitsValue(s, start) == (if s[start] == '1' then Pow2(|s| - 1 - start) else 0) + RightBitsValue(s, start + 1)
{
  // This follows directly from the definition
}