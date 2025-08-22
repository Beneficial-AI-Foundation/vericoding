//ATOM Add
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

//ATOM NormalizeBitString
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

//ATOM OStr2Int
// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}

//ATOM Str2Int
// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM ValidBitString
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
  Str2Int(s) == 0
}

/* code modified by LLM (iteration 1): Helper lemma for zero multiplication */
lemma ZeroMultiplicationLemma(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires IsZeroString(s1) || IsZeroString(s2)
  ensures Str2Int(s1) * Str2Int(s2) == 0
{
  // Follows from the definition of IsZeroString
}

/* code modified by LLM (iteration 1): Helper method to check if last bit is 1 */
function LastBitIsOne(s: string): bool
  requires ValidBitString(s)
{
  |s| > 0 && s[|s|-1] == '1'
}

/* code modified by LLM (iteration 1): Helper method to perform right shift */
method RightShift(s: string) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s) / 2
{
  if |s| <= 1 {
    result := "0";
    /* code modified by LLM (iteration 1): Assert correctness for short strings */
    if |s| == 0 {
      assert Str2Int(s) == 0;
      assert Str2Int(result) == 0;
    } else {
      assert Str2Int(s) <= 1;
      assert Str2Int(s) / 2 == 0;
      assert Str2Int(result) == 0;
    }
  } else {
    result := s[0..|s|-1];
    /* code modified by LLM (iteration 1): Assert the shift relationship */
    assert Str2Int(s) == 2 * Str2Int(result) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(result) == Str2Int(s) / 2;
  }
}

/* code modified by LLM (iteration 1): Helper lemma for loop invariant maintenance */
lemma LoopInvariantLemma(s1: string, s2: string, res: string, current: string, multiplier: string, newRes: string, newCurrent: string, newMultiplier: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(res) && ValidBitString(current) && ValidBitString(multiplier)
  requires ValidBitString(newRes) && ValidBitString(newCurrent) && ValidBitString(newMultiplier)
  requires Str2Int(res) + Str2Int(current) * Str2Int(multiplier) == Str2Int(s1) * Str2Int(s2)
  requires LastBitIsOne(multiplier) ==> Str2Int(newRes) == Str2Int(res) + Str2Int(current)
  requires !LastBitIsOne(multiplier) ==> Str2Int(newRes) == Str2Int(res)
  requires Str2Int(newCurrent) == 2 * Str2Int(current)
  requires Str2Int(newMultiplier) == Str2Int(multiplier) / 2
  ensures Str2Int(newRes) + Str2Int(newCurrent) * Str2Int(newMultiplier) == Str2Int(s1) * Str2Int(s2)
{
  if LastBitIsOne(multiplier) {
    calc {
      Str2Int(newRes) + Str2Int(newCurrent) * Str2Int(newMultiplier);
      ==
      (Str2Int(res) + Str2Int(current)) + (2 * Str2Int(current)) * (Str2Int(multiplier) / 2);
      ==
      Str2Int(res) + Str2Int(current) + Str2Int(current) * Str2Int(multiplier) - Str2Int(current);
      ==
      Str2Int(res) + Str2Int(current) * Str2Int(multiplier);
      ==
      Str2Int(s1) * Str2Int(s2);
    }
  } else {
    calc {
      Str2Int(newRes) + Str2Int(newCurrent) * Str2Int(newMultiplier);
      ==
      Str2Int(res) + (2 * Str2Int(current)) * (Str2Int(multiplier) / 2);
      ==
      Str2Int(res) + Str2Int(current) * Str2Int(multiplier);
      ==
      Str2Int(s1) * Str2Int(s2);
    }
  }
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
  /* code modified by LLM (iteration 1): Handle zero cases */
  if IsZeroString(s1) || IsZeroString(s2) {
    res := "0";
    ZeroMultiplicationLemma(s1, s2);
    return;
  }
  
  res := "0";
  var current := s1;
  var multiplier := s2;
  
  /* code modified by LLM (iteration 1): Main multiplication loop */
  while !IsZeroString(multiplier)
    invariant ValidBitString(res) && ValidBitString(current) && ValidBitString(multiplier)
    invariant Str2Int(res) + Str2Int(current) * Str2Int(multiplier) == Str2Int(s1) * Str2Int(s2)
    decreases Str2Int(multiplier)
  {
    /* code modified by LLM (iteration 1): Process least significant bit */
    if LastBitIsOne(multiplier) {
      res := Add(res, current);
    }
    
    /* code modified by LLM (iteration 1): Double current and halve multiplier */
    current := Add(current, current);
    var oldMultiplier := multiplier;
    multiplier := RightShift(multiplier);
    
    /* code modified by LLM (iteration 1): Prove loop invariant maintenance */
    LoopInvariantLemma(s1, s2, 
      if LastBitIsOne(oldMultiplier) then Add(res, s1) else res,
      s1, 
      oldMultiplier,
      res, 
      current, 
      multiplier);
  }
  
  /* code modified by LLM (iteration 1): Final assertion */
  assert IsZeroString(multiplier);
  assert Str2Int(multiplier) == 0;
  assert Str2Int(res) + Str2Int(current) * 0 == Str2Int(s1) * Str2Int(s2);
  assert Str2Int(res) == Str2Int(s1) * Str2Int(s2);
}