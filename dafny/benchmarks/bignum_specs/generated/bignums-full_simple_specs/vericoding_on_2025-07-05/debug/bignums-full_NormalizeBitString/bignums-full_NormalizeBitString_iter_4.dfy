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
  /* code modified by LLM (iteration 3): Handle empty string case */
  if |s| == 0 {
    t := "0";
    return;
  }
  
  /* code modified by LLM (iteration 3): Handle invalid bit string case */
  if !ValidBitString(s) {
    t := "0";
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 3): Find first non-zero character */
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant ValidBitString(s)
    invariant forall j | 0 <= j < i :: s[j] == '0'
  {
    i := i + 1;
  }
  
  if i == |s| {
    /* code modified by LLM (iteration 3): All characters are '0' */
    t := "0";
    AllZerosHaveValueZero(s);
  } else {
    /* code modified by LLM (iteration 3): Remove leading zeros */
    t := s[i..];
    /* code modified by LLM (iteration 3): Prove Str2Int equivalence */
    LeadingZerosPreserveValue(s, i);
  }
}

/* code modified by LLM (iteration 3): Fixed helper lemma for leading zeros */
lemma LeadingZerosPreserveValue(s: string, i: nat)
  requires ValidBitString(s)
  requires i < |s|
  requires forall j | 0 <= j < i :: s[j] == '0'
  ensures Str2Int(s) == Str2Int(s[i..])
  decreases i
{
  if i == 0 {
    assert s[i..] == s;
  } else {
    /* code modified by LLM (iteration 3): Inductive step */
    assert s[0] == '0';
    var s_tail := s[1..];
    assert ValidBitString(s_tail);
    assert forall j | 0 <= j < i-1 :: s_tail[j] == '0';
    
    if i == 1 {
      /* code modified by LLM (iteration 3): Base case for recursion */
      assert s[i..] == s[1..];
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      assert s[0] == '0';
      
      /* code modified by LLM (iteration 3): Show s[0..|s|-1] has same value as s[1..|s|-1] */
      if |s| > 1 {
        var prefix := s[0..|s|-1];
        var prefix_tail := s[1..|s|-1];
        assert prefix[0] == '0';
        assert prefix[1..] == prefix_tail;
        SingleLeadingZeroLemma(prefix);
        assert Str2Int(prefix) == Str2Int(prefix_tail);
        
        /* code modified by LLM (iteration 3): Reconstruct s[1..] value */
        assert s[1..] == prefix_tail + [s[|s|-1]];
        Str2IntSplit(s[1..]);
        assert Str2Int(s[1..]) == 2 * Str2Int(prefix_tail) + (if s[|s|-1] == '1' then 1 else 0);
        assert Str2Int(s) == 2 * Str2Int(prefix_tail) + (if s[|s|-1] == '1' then 1 else 0);
      } else {
        assert |s| == 1;
        assert s == "0";
        assert s[1..] == "";
        assert Str2Int(s) == 0;
        assert Str2Int(s[1..]) == 0;
      }
    } else {
      /* code modified by LLM (iteration 3): Recursive case */
      LeadingZerosPreserveValue(s_tail, i-1);
      assert Str2Int(s_tail) == Str2Int(s_tail[i-1..]);
      assert s_tail[i-1..] == s[i..];
      
      /* code modified by LLM (iteration 3): Connect s and s_tail values */
      SingleLeadingZeroLemma(s);
      assert Str2Int(s) == Str2Int(s_tail);
    }
  }
}

/* code modified by LLM (iteration 3): Lemma for removing a single leading zero */
lemma SingleLeadingZeroLemma(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
{
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    var prefix := s[0..|s|-1];
    var lastChar := s[|s|-1];
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if lastChar == '1' then 1 else 0);
    
    assert prefix[0] == '0';
    assert prefix[1..] == s[1..|s|-1];
    SingleLeadingZeroLemma(prefix);
    assert Str2Int(prefix) == Str2Int(prefix[1..]);
    
    /* code modified by LLM (iteration 3): Show s[1..] structure */
    assert s[1..] == prefix[1..] + [lastChar];
    Str2IntSplit(s[1..]);
    assert Str2Int(s[1..]) == 2 * Str2Int(prefix[1..]) + (if lastChar == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(prefix[1..]) + (if lastChar == '1' then 1 else 0);
  }
}

/* code modified by LLM (iteration 3): Helper lemma for Str2Int structure */
lemma Str2IntSplit(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
  // This follows directly from the definition of Str2Int
}

/* code modified by LLM (iteration 3): Lemma for all-zeros strings */
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
    assert ValidBitString(prefix);
    assert forall j | 0 <= j < |prefix| :: prefix[j] == '0';
    AllZerosHaveValueZero(prefix);
    assert Str2Int(prefix) == 0;
    assert s[|s|-1] == '0';
    assert Str2Int(s) == 2 * 0 + 0;
  }
}