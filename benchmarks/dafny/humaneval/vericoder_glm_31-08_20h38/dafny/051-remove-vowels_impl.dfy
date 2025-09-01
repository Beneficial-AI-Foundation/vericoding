

// <vc-helpers>
function isVowel(c: char): bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma in_string_substring(s: string, i: int, c: char)
    requires 0 <= i < |s| && s[i] == c
    ensures c in s
{
}

lemma non_vowel_in_result(text: string, i: int, result: string)
    requires 0 <= i < |text| && !isVowel(text[i]) && text[i] in result
    ensures text[i] in result
{
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
        invariant forall k: int :: 0 <= k < |result| ==> result[k] in text
        invariant forall k: int :: 0 <= k < |result| ==> !isVowel(result[k])
        invariant forall j: int :: 0 <= j < i && !isVowel(text[j]) ==> text[j] in result
    {
        if !isVowel(text[i])
        {
            result := result + [text[i]];
            in_string_substring(text, i, text[i]);
            non_vowel_in_result(text, i, result);
        }
    }
    return result;
}
// </vc-code>

