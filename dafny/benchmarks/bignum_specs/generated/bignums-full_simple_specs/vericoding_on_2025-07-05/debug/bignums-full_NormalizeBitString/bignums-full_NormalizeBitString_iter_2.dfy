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


//IMPL 

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  /* code modified by LLM (iteration 1): Handle empty string case and ensure valid bit string output */
  if |s| == 0 {
    t := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Add validation check for input string */
  if !ValidBitString(s) {
    t := "0";
    return;
  }
  
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    /* code modified by LLM (iteration 1): Add invariant to maintain valid bit string property */
    invariant ValidBitString(s)
  {
    i := i + 1;
  }
  
  if i == |s| {
    t := "0";
  } else {
    t := s[i..];
    /* code modified by LLM (iteration 1): Add assertion to help prove postconditions */
    assert ValidBitString(s) && i < |s|;
    assert ValidBitString(t);
    assert |t| > 0;
    assert i > 0 ==> |t| < |s|;
    assert i < |s| && s[i] != '0' ==> (|t| > 1 ==> t[0] != '0');
    /* code modified by LLM (iteration 1): Call helper lemma to prove Str2Int equivalence */
    if ValidBitString(s) {
      LeadingZerosPreserveValue(s, i);
    }
  }
}

/* code modified by LLM (iteration 1): Add helper lemma to prove that removing leading zeros preserves Str2Int value */
lemma LeadingZerosPreserveValue(s: string, i: nat)
  requires ValidBitString(s)
  requires i <= |s|
  requires forall j | 0 <= j < i :: s[j] == '0'
  ensures i == |s| ==> Str2Int(s) == 0
  ensures i < |s| ==> Str2Int(s) == Str2Int(s[i..])
{
  if i == 0 {
    assert s[i..] == s;
  } else if i == |s| {
    LeadingZerosAreZero(s, i);
  } else {
    assert i > 0 && i < |s|;
    LeadingZerosAreZero(s, i);
    assert Str2Int(s) == 0 + Str2Int(s[i..]);
  }
}

/* code modified by LLM (iteration 1): Add helper lemma to prove that strings of all zeros have Str2Int value 0 */
lemma LeadingZerosAreZero(s: string, i: nat)
  requires ValidBitString(s)
  requires i <= |s|
  requires forall j | 0 <= j < i :: s[j] == '0'
  ensures i == |s| ==> Str2Int(s) == 0
  ensures i < |s| ==> Str2Int(s) == Str2Int(s[i..])
  decreases i
{
  if i == 0 {
    // Base case: no leading zeros to remove
  } else if i == |s| {
    // All characters are '0'
    AllZerosHaveValueZero(s);
  } else {
    // i > 0 and i < |s|
    if |s| > 0 {
      var prefix := s[0..|s|-1];
      var lastChar := s[|s|-1];
      assert s == prefix + [lastChar];
      
      if i == |s| {
        AllZerosHaveValueZero(s);
      } else {
        // Use the recursive structure of Str2Int
        assert Str2Int(s) == 2 * Str2Int(prefix) + (if lastChar == '1' then 1 else 0);
        
        if i <= |prefix| {
          LeadingZerosAreZero(prefix, i);
          if i == |prefix| {
            assert Str2Int(prefix) == 0;
            assert lastChar == '0';  // since i < |s| and all chars up to i are '0'
            assert Str2Int(s) == 0;
            assert s[i..] == [lastChar];
            assert Str2Int(s[i..]) == 0;
          }
        }
      }
    }
  }
}

/* code modified by LLM (iteration 1): Add helper lemma to prove that a string of all zeros has Str2Int value 0 */
lemma AllZerosHaveValueZero(s: string)
  requires ValidBitString(s)
  requires forall j | 0 <= j < |s| :: s[j] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // Base case
  } else {
    var prefix := s[0..|s|-1];
    assert forall j | 0 <= j < |prefix| :: prefix[j] == '0';
    AllZerosHaveValueZero(prefix);
    assert Str2Int(prefix) == 0;
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * 0 + 0 == 0;
  }
}