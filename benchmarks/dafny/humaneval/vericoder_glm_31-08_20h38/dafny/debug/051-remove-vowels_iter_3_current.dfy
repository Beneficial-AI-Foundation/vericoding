

// <vc-helpers>
function isVowel(c: char): bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma in_string_substring(s: string, i: int, c: char)
    requires 0 <= i < |s| && s[i] == c
    ensures c in s
{
}

lemma substring_in_string(s: string, t: string)
    requires |s| == |t| && forall i : int :: 0 <= i < |s| ==> s[i] == t[i]
    ensures s == t
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
    {
        if !isVowel(text[i])
        {
            result := result + [text[i]];
            in_string_substring(text, i, text[i]);
        }
    }
    return result;
}
// </vc-code>

