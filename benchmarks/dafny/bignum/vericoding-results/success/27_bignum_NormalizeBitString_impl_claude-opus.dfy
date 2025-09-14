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

// <vc-helpers>
lemma Str2IntZero(s: string)
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
    assert |s| >= 2;
    var s_prefix := s[0..|s|-1];
    var s_last := s[|s|-1];
    
    calc {
      Str2Int(s);
      == 2 * Str2Int(s_prefix) + (if s_last == '1' then 1 else 0);
      == { assert s_prefix[0] == '0'; Str2IntZero(s_prefix); }
         2 * Str2Int(s_prefix[1..]) + (if s_last == '1' then 1 else 0);
      == { assert s_prefix[1..] == s[1..|s|-1]; }
         2 * Str2Int(s[1..|s|-1]) + (if s_last == '1' then 1 else 0);
      == { assert s[1..] == s[1..|s|-1] + [s_last]; }
         Str2Int(s[1..]);
    }
  }
}

lemma ValidBitStringSubstring(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
}
// </vc-helpers>

// <vc-spec>
method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
// </vc-spec>
// <vc-code>
{
  if !ValidBitString(s) {
    t := "0";
  } else if |s| == 0 {
    t := "0";
  } else {
    var i := 0;
    while i < |s| - 1 && s[i] == '0'
      invariant 0 <= i < |s|
      invariant forall j | 0 <= j < i :: s[j] == '0'
      invariant ValidBitString(s[i..])
      invariant Str2Int(s) == Str2Int(s[i..])
    {
      Str2IntZero(s[i..]);
      i := i + 1;
    }
    t := s[i..];
    ValidBitStringSubstring(s, i, |s|);
  }
}
// </vc-code>

