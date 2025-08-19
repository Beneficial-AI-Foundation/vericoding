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
  /* code modified by LLM (iteration 1): Handle empty strings as zero */
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Initialize result to zero and use simple bit-by-bit multiplication */
  res := "0";
  var i := 0;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    /* code modified by LLM (iteration 1): Maintain that result equals s1 * value of processed bits */
    invariant Str2Int(res) == Str2Int(s1) * ProcessedValue(s2, i)
  {
    /* code modified by LLM (iteration 1): Process bit from left to right */
    if s2[i] == '1' {
      var shift_amount := |s2| - 1 - i;
      var shifted_s1 := LeftShift(s1, shift_amount);
      res := Add(res, shifted_s1);
    }
    
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Apply lemma to establish final postcondition */
  ProcessedValueComplete(s2);
  
  res := NormalizeBitString(res);
}

/* code modified by LLM (iteration 1): Helper function to create left-shifted string */
function LeftShift(s: string, n: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(LeftShift(s, n))
  ensures Str2Int(LeftShift(s, n)) == Str2Int(s) * Power2(n)
{
  s + ZeroString(n)
}

/* code modified by LLM (iteration 1): Helper function to create string of zeros */
function ZeroString(n: nat): string
  ensures ValidBitString(ZeroString(n))
  ensures |ZeroString(n)| == n
  ensures Str2Int(ZeroString(n)) == 0
  decreases n
{
  if n == 0 then "" else ZeroString(n - 1) + "0"
}

/* code modified by LLM (iteration 1): Helper function for power of 2 */
function Power2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

/* code modified by LLM (iteration 1): Function to compute value of first k bits from left */
function ProcessedValue(s: string, k: nat): nat
  requires ValidBitString(s)
  requires 0 <= k <= |s|
  decreases k
{
  if k == 0 then 0
  else 
    var bit_pos := |s| - k;
    var bit_value := if s[k-1] == '1' then Power2(bit_pos) else 0;
    ProcessedValue(s, k-1) + bit_value
}

/* code modified by LLM (iteration 1): Lemma to prove ProcessedValue equals Str2Int for complete string */
lemma ProcessedValueComplete(s: string)
  requires ValidBitString(s)
  ensures ProcessedValue(s, |s|) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // Base case
  } else {
    // Inductive case
    var s_prefix := s[0..|s|-1];
    ProcessedValueComplete(s_prefix);
    
    /* code modified by LLM (iteration 1): Establish relationship between ProcessedValue and Str2Int */
    calc {
      ProcessedValue(s, |s|);
    ==
      ProcessedValue(s, |s|-1) + (if s[|s|-1] == '1' then Power2(0) else 0);
    ==
      ProcessedValue(s, |s|-1) + (if s[|s|-1] == '1' then 1 else 0);
    ==
      Str2Int(s_prefix) + (if s[|s|-1] == '1' then 1 else 0);
    ==
      2 * Str2Int(s_prefix) + (if s[|s|-1] == '1' then 1 else 0);
    ==
      Str2Int(s);
    }
  }
}