// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate is_vowel(c: char) { c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' }
// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)

    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
// </vc-spec>
// <vc-code>
{
  var result := "";
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall j : int :: 0 <= j < |result| ==> !is_vowel(result[j])
    invariant forall j : int :: 0 <= j < i && !is_vowel(text[j]) ==> text[j] in result
    invariant forall j : int :: 0 <= j < |result| ==> result[j] in text
  {
    if !is_vowel(text[i]) {
      result := result + text[i..i+1];
    }
    i := i + 1;
  }
  s := result;
}
// </vc-code>
