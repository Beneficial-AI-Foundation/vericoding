

// <vc-helpers>
predicate is_vowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma preserve_non_vowels(text: string, s: string, i: int)
    requires 0 <= i <= |text|
    requires s == text[..i][j := text[j] | j in set k | 0 <= k < i && !is_vowel(text[k])]
    requires forall k :: 0 <= k < i && !is_vowel(text[k]) ==> text[k] in s
    ensures forall j :: 0 <= j < i && !is_vowel(text[j]) ==> text[j] in s
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
    s := "";
    var i := 0;
    
    while i < |text|
        invariant 0 <= i <= |text|
        invariant forall j :: 0 <= j < |s| ==> !is_vowel(s[j])
        invariant forall j :: 0 <= j < |s| ==> s[j] in text
        invariant forall j :: 0 <= j < i && !is_vowel(text[j]) ==> text[j] in s
    {
        if !is_vowel(text[i]) {
            s := s + [text[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

