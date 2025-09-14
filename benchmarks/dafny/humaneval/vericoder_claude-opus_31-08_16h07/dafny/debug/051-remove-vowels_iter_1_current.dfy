

// <vc-helpers>
predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma SubstringPreservesNonVowels(text: string, result: string, i: int)
    requires 0 <= i <= |text|
    requires result == text[..i]
    requires forall k :: 0 <= k < |result| ==> !IsVowel(result[k])
    requires forall k :: 0 <= k < |result| ==> result[k] in text
    requires forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in result
    ensures forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in result
{
    // This lemma helps maintain the invariant
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
        invariant forall k :: 0 <= k < |s| ==> !IsVowel(s[k])
        invariant forall k :: 0 <= k < |s| ==> s[k] in text
        invariant forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in s
    {
        if !IsVowel(text[i]) {
            s := s + [text[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

