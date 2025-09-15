// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for better practice */
predicate IsVowel(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}
// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)

    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added invariant i <= |text| to resolve compilation errors */
  s := "";
  var i := 0;
  while i < |text|
    invariant i <= |text|
    invariant |s| <= i
    invariant forall k :: 0 <= k < |s| ==> !IsVowel(s[k])
    invariant forall k :: 0 <= k < |s| ==> s[k] in text[..i]
    invariant forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in s
  {
    if !IsVowel(text[i]) {
      s := s + [text[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
