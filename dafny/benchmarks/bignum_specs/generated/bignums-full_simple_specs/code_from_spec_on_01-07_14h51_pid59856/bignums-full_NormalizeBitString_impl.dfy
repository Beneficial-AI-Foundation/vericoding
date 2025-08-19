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


//IMPL NormalizeBitString

/* code modified by LLM (iteration 7): Added helper lemma to prove substring validity */
lemma SubstringValidBitString(s: string, start: int, end: int)
  requires ValidBitString(s)
  requires 0 <= start <= end <= |s|
  ensures ValidBitString(s[start..end])
{
  // Dafny can prove this automatically
}

/* code modified by LLM (iteration 7): Helper lemma for all-zeros case */
lemma AllZerosGiveZero(s: string)
  requires ValidBitString(s)
  requires forall j | 0 <= j < |s| :: s[j] == '0'
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    assert s[|s|-1] == '0';
    assert forall j | 0 <= j < |s|-1 :: s[j] == '0';
    SubstringValidBitString(s, 0, |s|-1);
    AllZerosGiveZero(s[0..|s|-1]);
  }
}

/* code modified by LLM (iteration 7): Simplified lemma for removing leading zero */
lemma LeadingZeroRemoval(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  decreases |s|
{
  SubstringValidBitString(s, 1, |s|);
  
  if |s| == 1 {
    // s = "0", s[1..] = ""
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    // |s| >= 2, so both s and s[1..] are non-empty
    // We'll prove this by showing the mathematical relationship
    
    // First establish what we're working with
    var s_prefix := s[0..|s|-1];  // all but last char
    var s_suffix := s[1..];       // all but first char  
    var last_char := s[|s|-1];
    
    SubstringValidBitString(s, 0, |s|-1);
    
    // Key insight: s_prefix[1..] == s_suffix[0..|s_suffix|-1] when |s| >= 2
    if |s| >= 2 {
      assert s_prefix == s[0..|s|-1];
      assert s_suffix == s[1..];
      assert |s_suffix| == |s| - 1;
      
      if |s_suffix| > 0 {
        assert s_suffix[0..|s_suffix|-1] == s[1..|s|-1];
        assert s_prefix[1..] == s[0..|s|-1][1..] == s[1..|s|-1];
        assert s_prefix[1..] == s_suffix[0..|s_suffix|-1];
        
        // Since s[0] == '0', we have s_prefix[0] == '0'
        SubstringValidBitString(s_prefix, 1, |s_prefix|);
        LeadingZeroRemoval(s_prefix);
        
        // Now we can compute:
        calc {
          Str2Int(s);
          == 2 * Str2Int(s_prefix) + (if last_char == '1' then 1 else 0);
          == { LeadingZeroRemoval(s_prefix); }
          2 * Str2Int(s_prefix[1..]) + (if last_char == '1' then 1 else 0);
          == 2 * Str2Int(s_suffix[0..|s_suffix|-1]) + (if s_suffix[|s_suffix|-1] == '1' then 1 else 0);
          == Str2Int(s_suffix);
        }
      } else {
        // |s_suffix| == 0, so s has length 1, contradiction
        assert false;
      }
    }
  }
}

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  if |s| == 0 {
    t := "0";
    return;
  }
  
  if !ValidBitString(s) {
    t := "0";
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 7): Simplified loop with cleaner invariants */
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
    invariant Str2Int(s) == Str2Int(s[i..])
  {
    /* code modified by LLM (iteration 7): Maintain invariant with leading zero removal */
    SubstringValidBitString(s, i, |s|);
    LeadingZeroRemoval(s[i..]);
    i := i + 1;
  }
  
  if i == |s| {
    // All zeros
    t := "0";
    /* code modified by LLM (iteration 7): Use all-zeros lemma */
    AllZerosGiveZero(s);
    assert Str2Int(t) == 0;
  } else {
    // Found first non-zero at position i
    t := s[i..];
    /* code modified by LLM (iteration 7): Postconditions follow from loop invariants */
    SubstringValidBitString(s, i, |s|);
    assert s[i] != '0'; // from loop exit condition
    assert Str2Int(s) == Str2Int(t); // from loop invariant
  }
}