

// <vc-helpers>
function IsVowel(c: char): bool
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate method {:pure} IsOnlyConsonants(s: string)
    reads s
{
    forall i :: 0 <= i < |s| ==> !IsVowel(s[i])
}

function method RemoveVowelsUpTo(text: string, index: int): string
    requires 0 <= index <= |text|
    ensures IsOnlyConsonants(RemoveVowelsUpTo(text, index))
{
    var result_chars := "";
    for i := 0 to index - 1
        invariant 0 <= i <= index -1
        invariant IsOnlyConsonants(result_chars)
    {
        if !IsVowel(text[i]) {
            result_chars := result_chars + text[i];
        }
    }
    return result_chars;
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
    var resultSeq := "";
    for i := 0 to |text|
        invariant 0 <= i <= |text|
        invariant IsOnlyConsonants(resultSeq)
        invariant forall j : int :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in resultSeq
        invariant forall j : int :: 0 <= j < |resultSeq| ==> resultSeq[j] in text
        invariant resultSeq == RemoveVowelsUpTo(text, i)
    {
        if !IsVowel(text[i]) {
            resultSeq := resultSeq + text[i];
        }
    }
    s := resultSeq;
}
// </vc-code>

