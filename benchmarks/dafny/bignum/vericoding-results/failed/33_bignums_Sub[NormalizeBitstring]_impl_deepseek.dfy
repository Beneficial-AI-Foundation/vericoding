ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function AbsDiff(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(AbsDiff(s1, s2))
  ensures Str2Int(AbsDiff(s1, s2)) == Str2Int(s1) - Str2Int(s2)
  decreases |s1| + |s2|
{
  if |s2| == 0 then s1
  else if |s1| == 0 then ""
  else
    var s1_last := s1[|s1|-1];
    var s2_last := s2[|s2|-1];
    var s1_prefix := s1[0..|s1|-1];
    var s2_prefix := s2[0..|s2|-1];
    assert ValidBitString(s1_prefix);
    assert ValidBitString(s2_prefix);
    var rest := AbsDiff(s1_prefix, s2_prefix);
    if (s1_last == '1' && s2_last == '0') || (s1_last == '0' && s2_last == '0') || (s1_last == '1' && s2_last == '1') then
      rest + [if s1_last == s2_last then '0' else '1']
    else
      var borrow_rest := AbsDiff(rest, "1");
      borrow_rest + ['1']
}

lemma AbsDiffPreservesValidBitString(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(AbsDiff(s1, s2))
{
  if |s2| != 0 && |s1| != 0 {
    var s1_prefix := s1[0..|s1|-1];
    var s2_prefix := s2[0..|s2|-1];
    assert ValidBitString(s1_prefix);
    assert ValidBitString(s2_prefix);
    AbsDiffPreservesValidBitString(s1_prefix, s2_prefix);
    
    var rest := AbsDiff(s1_prefix, s2_prefix);
    if (s1[|s1|-1] == '1' && s2[|s2|-1] == '0') || (s1[|s1|-1] == '0' && s2[|s2|-1] == '0') || (s1[|s1|-1] == '1' && s2[|s2|-1] == '1') {
      // Adding '0' or '1' to valid bit string gives valid bit string
    } else {
      AbsDiffPreservesValidBitString(rest, "1");
    }
  }
}

lemma AbsDiffCorrect(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures Str2Int(AbsDiff(s1, s2)) == Str2Int(s1) - Str2Int(s2)
{
  if |s2| != 0 && |s1| != 0 {
    var s1_last := s1[|s1|-1];
    var s2_last := s2[|s2|-1];
    var s1_prefix := s1[0..|s1|-1];
    var s2_prefix := s2[0..|s2|-1];
    
    AbsDiffCorrect(s1_prefix, s2_prefix);
    var rest := AbsDiff(s1_prefix, s2_prefix);
    
    if (s1_last == '1' && s2_last == '0') || (s1_last == '0' && s2_last == '0') || (s1_last == '1' && s2_last == '1') {
      // Rest case handles the math correctly
    } else {
      AbsDiffCorrect(rest, "1");
    }
  }
}

ghost method NormalizeBitStringImpl(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  if |s| == 0 {
    t := "0";
  } else if s[0] == '0' {
    var rest := s[1..];
    t := NormalizeBitStringImpl(rest);
  } else {
    t := s;
  }
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var diff := AbsDiff(s1, s2);
  AbsDiffPreservesValidBitString(s1, s2);
  AbsDiffCorrect(s1, s2);
  
  var t := diff;
  // Remove leading zeros if any
  var i := 0;
  while i < |t| && t[i] == '0' 
    invariant i <= |t|
    invariant forall j | 0 <= j < i :: t[j] == '0'
  {
    i := i + 1;
  }
  
  if i == |t| {
    // All zeros, return "0"
    t := "0";
  } else {
    t := t[i..];
  }
  
  return t;
}
// </vc-code>

