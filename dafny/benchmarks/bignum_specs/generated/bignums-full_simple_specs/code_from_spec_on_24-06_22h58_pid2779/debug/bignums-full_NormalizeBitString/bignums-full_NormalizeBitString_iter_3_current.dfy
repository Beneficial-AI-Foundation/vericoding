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

/* code modified by LLM (iteration 2): simplified lemma to prove that removing leading zeros preserves value */
lemma RemoveLeadingZeroPreservesValue(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
{
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert s[0] == '0';
    
    // Show that s[0..|s|-1] with leading zero removed equals s[1..][0..|s[1..]|-1]
    var s_without_last := s[0..|s|-1];
    var s_without_first := s[1..];
    
    assert s_without_last == s[0] + s[1..|s|-1];
    assert s_without_first == s[1..];
    
    if |s_without_last| > 0 && s_without_last[0] == '0' {
      RemoveLeadingZeroPreservesValue(s_without_last);
      assert Str2Int(s_without_last) == Str2Int(s_without_last[1..]);
      assert s_without_last[1..] == s[1..|s|-1];
    }
    
    assert Str2Int(s[1..]) == 2 * Str2Int(s[1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    
    if s_without_last == "0" {
      assert Str2Int(s_without_last) == 0;
      assert s[1..|s|-1] == "";
      assert Str2Int(s[1..|s|-1]) == 0;
    } else if |s_without_last| > 0 && s_without_last[0] == '0' {
      assert Str2Int(s_without_last) == Str2Int(s[1..|s|-1]);
    } else {
      assert s_without_last == s[1..|s|-1];
      assert Str2Int(s_without_last) == Str2Int(s[1..|s|-1]);
    }
  }
}

/* code modified by LLM (iteration 2): lemma to handle multiple leading zeros */
lemma RemoveAllLeadingZerosPreservesValue(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall j | 0 <= j < i :: s[j] == '0'
  ensures Str2Int(s) == Str2Int(s[i..])
  decreases i
{
  if i == 0 {
    assert s[i..] == s;
  } else {
    RemoveAllLeadingZerosPreservesValue(s, i-1);
    assert Str2Int(s) == Str2Int(s[i-1..]);
    if i-1 < |s| {
      assert s[i-1] == '0';
      RemoveLeadingZeroPreservesValue(s[i-1..]);
      assert Str2Int(s[i-1..]) == Str2Int(s[i..]);
    }
  }
}

method NormalizeBitString(s: string) returns(t: string)
  requires ValidBitString(s)
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
  
  // Find the first non-zero character
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant forall j | 0 <= j < i :: s[j] == '0'
  {
    i := i + 1;
  }
  
  if i == |s| {
    // All characters are '0', return "0"
    t := "0";
    /* code modified by LLM (iteration 2): simplified verification for all-zeros case */
    assert forall j | 0 <= j < |s| :: s[j] == '0';
    assert Str2Int("0") == 0;
    if |s| > 0 {
      RemoveAllLeadingZerosPreservesValue(s, |s|);
      assert s[|s|..] == "";
      assert Str2Int(s) == Str2Int("") == 0;
    }
  } else {
    // Return substring from first non-zero character
    t := s[i..];
    /* code modified by LLM (iteration 2): use simplified lemma */
    RemoveAllLeadingZerosPreservesValue(s, i);
    assert ValidBitString(t);
    assert |t| > 0;
    assert i < |s| && s[i] != '0';
    assert t[0] == s[i] != '0';
  }
}