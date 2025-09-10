

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := "";
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall p :: 0 <= p < |s| ==> s[p] != 'a' && s[p] != 'e' && s[p] != 'i' && s[p] != 'o' && s[p] != 'u'
    invariant forall p :: 0 <= p < |s| ==> exists j :: 0 <= j < i && text[j] == s[p]
    invariant forall j :: 0 <= j < i && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> exists p :: 0 <= p < |s| && s[p] == text[j]
    decreases |text| - i
  {
    if text[i] != 'a' && text[i] != 'e' && text[i] != 'i' && text[i] != 'o' && text[i] != 'u' {
      s := s + [text[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

