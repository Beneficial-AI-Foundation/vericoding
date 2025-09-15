// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsLowerVowel(c: char) { c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' }
// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)

    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := "";
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall k :: 0 <= k < |s| ==> s[k] != 'a' && s[k] != 'e' && s[k] != 'i' && s[k] != 'o' && s[k] != 'u'
    invariant forall k :: 0 <= k < |s| ==> s[k] in text
    invariant forall j :: 0 <= j < i && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
  {
    if text[i] == 'a' || text[i] == 'e' || text[i] == 'i' || text[i] == 'o' || text[i] == 'u' {
      // skip vowel
    } else {
      s := s + text[i..i+1];
    }
    i := i + 1;
  }
}
// </vc-code>
