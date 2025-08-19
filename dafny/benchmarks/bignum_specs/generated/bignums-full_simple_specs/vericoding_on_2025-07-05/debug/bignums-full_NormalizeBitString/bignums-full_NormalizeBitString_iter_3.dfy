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
  /* code modified by LLM (iteration 2): Handle empty string case */
  if |s| == 0 {
    t := "0";
    return;
  }
  
  /* code modified by LLM (iteration 2): Handle invalid bit string case */
  if !ValidBitString(s) {
    t := "0";
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 2): Find first non-zero character */
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant ValidBitString(s)
    invariant forall j | 0 <= j < i :: s[j] == '0'
  {
    i := i + 1;
  }
  
  if i == |s| {
    /* code modified by LLM (iteration 2): All characters are '0' */
    t := "0";
    assert ValidBitString(t);
    assert |t| == 1;
    AllZerosHaveValueZero(s);
    assert Str2Int(s) == 0;
    assert Str2Int(t) == 0;
  } else {
    /* code modified by LLM (iteration 2): Remove leading zeros */
    t := s[i..];
    assert ValidBitString(s[i..]);
    assert |s[i..]| == |s| - i;
    assert i < |s|;
    assert |t| > 0;
    assert s[i] != '0';
    if |t| > 1 {
      assert t[0] == s[i];
      assert t[0] != '0';
    }
    /* code modified by LLM (iteration 2): Prove Str2Int equivalence */
    LeadingZerosPreserveValue(s, i);
  }
}

/* code modified by LLM (iteration 2): Simplified helper lemma for leading zeros */
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
    /* code modified by LLM (iteration 2): Use induction on the structure of Str2Int */
    var prefix := s[0..|s|-1];
    var lastChar := s[|s|-1];
    
    assert ValidBitString(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + (if lastChar == '1' then 1 else 0);
    
    if i <= |prefix| {
      /* code modified by LLM (iteration 2): Recursive case when i affects prefix */
      LeadingZerosPreserveValue(prefix, i);
      assert Str2Int(prefix) == Str2Int(prefix[i..]);
      
      /* code modified by LLM (iteration 2): Show that s[i..] can be reconstructed */
      if i == |prefix| {
        assert prefix[i..] == "";
        assert Str2Int(prefix[i..]) == 0;
        assert s[i..] == [lastChar];
        assert lastChar == '0';
        assert Str2Int(s[i..]) == 0;
        assert Str2Int(s) == 2 * 0 + 0 == 0;
      } else {
        assert s[i..] == prefix[i..] + [lastChar];
        Str2IntConcatenation(prefix[i..], lastChar);
        assert Str2Int(s[i..]) == 2 * Str2Int(prefix[i..]) + (if lastChar == '1' then 1 else 0);
        assert Str2Int(s) == 2 * Str2Int(prefix[i..]) + (if lastChar == '1' then 1 else 0);
      }
    } else {
      /* code modified by LLM (iteration 2): Case when i > |prefix| */
      assert i == |s|;
      assert false; // This contradicts i < |s|
    }
  }
}

/* code modified by LLM (iteration 2): Helper lemma for string concatenation and Str2Int */
lemma Str2IntConcatenation(prefix: string, lastChar: char)
  requires ValidBitString(prefix + [lastChar])
  ensures Str2Int(prefix + [lastChar]) == 2 * Str2Int(prefix) + (if lastChar == '1' then 1 else 0)
{
  var s := prefix + [lastChar];
  assert |s| > 0;
  assert s[0..|s|-1] == prefix;
  assert s[|s|-1] == lastChar;
}

/* code modified by LLM (iteration 2): Simplified lemma for all-zeros strings */
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