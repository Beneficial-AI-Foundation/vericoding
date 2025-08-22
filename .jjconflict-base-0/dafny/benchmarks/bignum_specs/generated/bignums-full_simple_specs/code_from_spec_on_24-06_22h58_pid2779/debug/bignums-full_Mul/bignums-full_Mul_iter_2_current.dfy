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
  /* code modified by LLM (iteration 1): Handle empty string cases and fix string comparison logic */
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Check for zero multiplicands using proper string comparison */
  if IsZeroString(s1) || IsZeroString(s2) {
    res := "0";
    return;
  }
  
  res := "0";
  var current := s1;
  var multiplier := s2;
  
  /* code modified by LLM (iteration 1): Fixed loop condition and added proper termination */
  while !IsZeroString(multiplier)
    invariant ValidBitString(res) && ValidBitString(current) && ValidBitString(multiplier)
    invariant Str2Int(res) + Str2Int(current) * Str2Int(multiplier) == Str2Int(s1) * Str2Int(s2)
    decreases Str2Int(multiplier)
  {
    /* code modified by LLM (iteration 1): Check least significant bit properly */
    if |multiplier| > 0 && multiplier[|multiplier|-1] == '1' {
      res := Add(res, current);
    }
    
    /* code modified by LLM (iteration 1): Double current using Add method */
    current := Add(current, current);
    
    /* code modified by LLM (iteration 1): Implement proper right shift for binary string */
    multiplier := RightShift(multiplier);
  }
}

/* code modified by LLM (iteration 1): Helper method to check if a bit string represents zero */
predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}

/* code modified by LLM (iteration 1): Helper method to perform right shift on bit string */
method RightShift(s: string) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures |s| <= 1 ==> Str2Int(result) == 0
  ensures |s| > 1 ==> Str2Int(result) == Str2Int(s) / 2
{
  if |s| <= 1 {
    result := "0";
  } else {
    result := s[0..|s|-1];
  }
}