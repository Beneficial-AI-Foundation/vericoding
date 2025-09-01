

// <vc-helpers>
function isVowel(c: char) returns (b: bool)
    ensures b == (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
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
var s := "";
var i := 0;
while i < |text|
    invariant i <= |text|
    invariant forall j : int :: 0 <= j < |s| ==> exists k : int :: 0 <= k < i && s[j] == text[k]
    invariant forall k : int :: 0 <= k < i && !isVowel(text[k]) ==> exists j : int :: 0 <= j < |s| && s[j] == text[k]
{
    if !isVowel(text[i]) {
        s := s + text[i];
    }
    i := i + 1;
}
return s;
// </vc-code>

