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

/* code modified by LLM (iteration 1): Helper predicate to check if a bit string represents zero */
predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}

/* code modified by LLM (iteration 1): Helper lemma for zero string property */
lemma IsZeroStringCorrect(s: string)
  requires ValidBitString(s)
  ensures IsZeroString(s) <==> Str2Int(s) == 0
{
  if |s| == 0 {
    // Empty string case is trivial
  } else {
    // Prove by induction on string structure
    if forall i | 0 <= i < |s| :: s[i] == '0' {
      Str2IntAllZeros(s);
    } else {
      Str2IntNotAllZeros(s);
    }
  }
}

/* code modified by LLM (iteration 1): Helper lemma for all-zeros string */
lemma Str2IntAllZeros(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires forall i | 0 <= i < |s| :: s[i] == '0'
  ensures Str2Int(s) == 0
  decreases s
{
  if |s| == 1 {
    // Base case: single '0' character
  } else {
    // Inductive case
    Str2IntAllZeros(s[0..|s|-1]);
  }
}

/* code modified by LLM (iteration 1): Helper lemma for not-all-zeros string */
lemma Str2IntNotAllZeros(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires exists i | 0 <= i < |s| :: s[i] == '1'
  ensures Str2Int(s) > 0
  decreases s
{
  if |s| == 1 {
    // Base case: single '1' character
  } else {
    if s[|s|-1] == '1' {
      // Last bit is 1, so result is odd and > 0
    } else {
      // Last bit is 0, but some earlier bit is 1
      Str2IntNotAllZeros(s[0..|s|-1]);
    }
  }
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
    /* code modified by LLM (iteration 1): Assert relationship between original and shifted string */
    RightShiftCorrect(s);
  }
}

/* code modified by LLM (iteration 1): Helper lemma for right shift correctness */
lemma RightShiftCorrect(s: string)
  requires ValidBitString(s)
  requires |s| > 1
  ensures ValidBitString(s[0..|s|-1])
  ensures Str2Int(s[0..|s|-1]) == Str2Int(s) / 2
{
  // The relationship follows directly from the definition of Str2Int
  var prefix := s[0..|s|-1];
  var lastBit := if s[|s|-1] == '1' then 1 else 0;
  assert Str2Int(s) == 2 * Str2Int(prefix) + lastBit;
  assert Str2Int(s) / 2 == Str2Int(prefix);
}

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Handle empty string cases */
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Check for zero multiplicands using helper predicate */
  IsZeroStringCorrect(s1);
  IsZeroStringCorrect(s2);
  
  if IsZeroString(s1) || IsZeroString(s2) {
    res := "0";
    return;
  }
  
  res := "0";
  var current := s1;
  var multiplier := s2;
  
  /* code modified by LLM (iteration 1): Fixed loop with proper invariants and termination */
  while !IsZeroString(multiplier)
    invariant ValidBitString(res) && ValidBitString(current) && ValidBitString(multiplier)
    invariant Str2Int(res) + Str2Int(current) * Str2Int(multiplier) == Str2Int(s1) * Str2Int(s2)
    decreases Str2Int(multiplier)
  {
    /* code modified by LLM (iteration 1): Check least significant bit and add if needed */
    if |multiplier| > 0 && multiplier[|multiplier|-1] == '1' {
      res := Add(res, current);
    }
    
    /* code modified by LLM (iteration 1): Double current value */
    current := Add(current, current);
    
    /* code modified by LLM (iteration 1): Right shift multiplier */
    var oldMultiplier := multiplier;
    multiplier := RightShift(multiplier);
    
    /* code modified by LLM (iteration 1): Maintain loop invariant with ghost steps */
    ghost var oldRes := res;
    ghost var oldCurrent := current;
    IsZeroStringCorrect(multiplier);
  }
}