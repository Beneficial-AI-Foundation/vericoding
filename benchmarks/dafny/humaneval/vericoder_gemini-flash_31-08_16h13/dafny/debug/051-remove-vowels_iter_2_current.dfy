

// <vc-helpers>
function IsVowel(c: char): bool
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
    var result := "";
    for i := 0 to |text|
        invariant 0 <= i <= |text|
        invariant forall j : int :: 0 <= j < |result| ==> !IsVowel(result[j])
        invariant forall j : int :: 0 <= j < |result| ==> result[j] in text
        invariant forall j : int :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in result
        invariant result == new_string_from_chars(RemoveVowelsUpTo(text, i))
    {
        if !IsVowel(text[i]) {
            result := result + text[i];
        }
    }
    s := result;
}
// </vc-code>

