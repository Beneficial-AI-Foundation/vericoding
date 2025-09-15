// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsVowel(c: char) {
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
  /* code modified by LLM (iteration 3): fixed type error in string concatenation */
  var result := "";
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall j: int :: 0 <= j < |result| ==> !IsVowel(result[j])
    invariant forall j: int :: 0 <= j < |result| ==> result[j] in text
    invariant forall j: int :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in result
  {
    if !IsVowel(text[i]) {
      result := result + [text[i]];
    }
    i := i + 1;
  }
  s := result;
}
// </vc-code>
