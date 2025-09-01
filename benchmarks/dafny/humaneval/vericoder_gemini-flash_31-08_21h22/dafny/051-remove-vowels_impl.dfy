

// <vc-helpers>
function is_vowel(c: char): bool {
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
    var new_s := new char[|text|];
    var k := 0;
    for i := 0 to |text|
        invariant 0 <= i <= |text|
        invariant 0 <= k <= i
        invariant forall j : int :: 0 <= j < k ==> !is_vowel(new_s[j])
        invariant forall j : int :: 0 <= j < k ==> exists l : int :: 0 <= l < i && text[l] == new_s[j] && !is_vowel(text[l])
        invariant forall j : int :: 0 <= j < i && !is_vowel(text[j]) ==> text[j] in new_s[..k]
        invariant forall j : int :: 0 <= j < k ==> new_s[j] in text[..i]
    {
        var c := text[i];
        if !is_vowel(c) {
            new_s[k] := c;
            k := k + 1;
        }
    }
    s := new_s[..k];
}
// </vc-code>

