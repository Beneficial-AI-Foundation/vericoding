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

/* code modified by LLM (iteration 3): fixed lemma to properly handle string slicing and validation */
lemma RemoveLeadingZeroPreservesValue(s: string)
  requires ValidBitString(s)
  requires |s| > 0 && s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
  ensures ValidBitString(s[1..])
{
  // First establish that s[1..] is a valid bit string
  assert forall i | 0 <= i < |s[1..]| :: s[1..][i] == s[i+1] && (s[i+1] == '0' || s[i+1] == '1');
  
  if |s| == 1 {
    assert s == "0";
    assert s[1..] == "";
    assert Str2Int(s) == 0;
    assert Str2Int(s[1..]) == 0;
  } else {
    // For |s| > 1, we need to show the recursive relationship
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s[1..]) == 2 * Str2Int(s[1..][0..|s[1..]|-1]) + (if s[1..][|s[1..]|-1] == '1' then 1 else 0);
    
    // Key insight: s[0..|s|-1] = "0" + s[1..|s|-1], and s[1..][0..|s[1..]|-1] = s[1..|s|-1]
    assert s[1..][0..|s[1..]|-1] == s[1..|s|-1];
    assert s[1..][|s[1..]|-1] == s[|s|-1];
    
    // Since s[0] == '0', we have s[0..|s|-1] starting with '0'
    var prefix := s[0..|s|-1];
    assert ValidBitString(prefix);
    assert prefix[0] == '0';
    
    if |prefix| > 0 {
      RemoveLeadingZeroPreservesValue(prefix);
      assert Str2Int(prefix) == Str2Int(prefix[1..]);
      assert prefix[1..] == s[1..|s|-1];
    }
  }
}

/* code modified by LLM (iteration 3): simplified and fixed lemma for multiple leading zeros */
lemma RemoveAllLeadingZerosPreservesValue(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  requires forall j | 0 <= j < i :: s[j] == '0'
  ensures Str2Int(s) == Str2Int(s[i..])
  ensures ValidBitString(s[i..])
  decreases i
{
  // Establish that s[i..] is valid
  assert forall k | 0 <= k < |s[i..]| :: s[i..][k] == s[i+k] && (s[i+k] == '0' || s[i+k] == '1');
  
  if i == 0 {
    assert s[i..] == s;
  } else {
    assert i > 0;
    RemoveAllLeadingZerosPreservesValue(s, i-1);
    assert Str2Int(s) == Str2Int(s[i-1..]);
    assert ValidBitString(s[i-1..]);
    
    if i-1 < |s| {
      assert s[i-1] == '0';
      assert |s[i-1..]| > 0 && s[i-1..][0] == '0';
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
    /* code modified by LLM (iteration 3): added validation for empty input case */
    assert ValidBitString(t);
    assert Str2Int("") == 0 && Str2Int("0") == 0;
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
    /* code modified by LLM (iteration 3): fixed verification for all-zeros case */
    assert forall j | 0 <= j < |s| :: s[j] == '0';
    assert ValidBitString(t);
    RemoveAllLeadingZerosPreservesValue(s, |s|);
    assert s[|s|..] == "";
    assert Str2Int(s) == Str2Int("") == 0;
    assert Str2Int(t) == 0;
  } else {
    // Return substring from first non-zero character
    t := s[i..];
    /* code modified by LLM (iteration 3): use corrected lemma */
    RemoveAllLeadingZerosPreservesValue(s, i);
    assert ValidBitString(t);
    assert |t| > 0;
    assert i < |s| && s[i] != '0';
    assert t[0] == s[i] != '0';
    if |t| > 1 {
      assert t[0] != '0';
    }
  }
}