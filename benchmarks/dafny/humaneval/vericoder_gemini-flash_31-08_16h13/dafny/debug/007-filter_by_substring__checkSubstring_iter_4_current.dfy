

// <vc-helpers>
function IsSubstring(s: string, sub: string): bool
  reads s, sub
{
  if |sub| == 0 then true
  else if |s| < |sub| then false
  else if s[0] == sub[0] && IsSubstring(s[1..], sub[1..]) then true
  else IsSubstring(s[1..], sub)
}

lemma IsSubstring_Property(s: string, sub: string)
  requires IsSubstring(s, sub)
  ensures exists i :: 0 <= i <= |s| - |sub| && s[i..i+|sub|] == sub
{
  if |sub| == 0 {
    assert true; // An empty string is a substring of any string, starting at index 0
  } else if |s| < |sub| {
    // This case should not be reached if IsSubstring(s,sub) is true
  } else if s[0] == sub[0] && IsSubstring(s[1..], sub[1..]) {
    IsSubstring_Property(s[1..], sub[1..]);
  } else {
    IsSubstring_Property(s[1..], sub);
  }
}

lemma IsSubstring_Property_Alternative(s: string, sub: string)
  ensures IsSubstring(s, sub) <==> (exists i :: 0 <= i && i + |sub| <= |s| && s[i..i+|sub|] == sub)
{
  if |sub| == 0 {
    assert IsSubstring(s, sub);
  } else if |s| < |sub| {
    assert !IsSubstring(s, sub);
    assert forall i :: !(0 <= i && i + |sub| <= |s| && s[i..i+|sub|] == sub);
  } else {
    if IsSubstring(s, sub) {
      if s[0] == sub[0] && IsSubstring(s[1..], sub[1..]) {
        IsSubstring_Property_Alternative(s[1..], sub[1..]);
        assert (exists j :: 0 <= j && j + |sub[1..]| <= |s[1..]| && s[1..][j..j+|sub[1..]|] == sub[1..]);
        var j_witness := (choose j : int such that 0 <= j && j + |sub[1..]| <= |s[1..]| && s[1..][j..j+|sub[1..]|] == sub[1..]);
        var i_witness := j_witness;
        assert 0 + i_witness + |sub[1..]| <= |s[1..]|;
        assert s[1..][i_witness..i_witness+|sub[1..]|] == sub[1..];
        assert s[0] == sub[0];
        assert s[0..|sub|] == sub;
      } else {
        assert IsSubstring(s[1..], sub);
        IsSubstring_Property_Alternative(s[1..], sub);
        assert (exists j : int :: 0 <= j && j + |sub| <= |s[1..]| && s[1..][j..j+|sub|] == sub);
        var j_witness := (choose j : int such that 0 <= j && j + |sub| <= |s[1..]| && s[1..][j..j+|sub|] == sub);
        var i_witness := 1 + j_witness;
        assert 0 <= j_witness && j_witness + |sub| <= |s[1..]|;
        assert s[1..][j_witness..j_witness+|sub|] == sub;
        assert s[1 + j_witness .. 1 + j_witness + |sub|] == sub;
      }
    } else {
      assert forall i :: !(0 <= i && i + |sub| <= |s| && s[i..i+|sub|] == sub);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method checkSubstring(s: string, sub: string) returns (result: bool)
// </vc-spec>
// <vc-code>
{
  result := IsSubstring(s, sub);
  IsSubstring_Property_Alternative(s, sub);
}
// </vc-code>

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
  assume{:axiom} false;
}