

// <vc-helpers>
function is_vowel(c: char): bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}
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
  var res: seq<char> := [];
  for i := 0 to |text|
    invariant 0 <= i <= |text|
    invariant forall j :: 0 <= j < |res| ==> !is_vowel(res[j])
    invariant forall j :: 0 <= j < |res| ==> exists l :: 0 <= l < i && res[j] == text[l]
  {
    if !is_vowel(text[i]) {
      res := res + [text[i]];
    }
  }
  s := res;
}
// </vc-code>

