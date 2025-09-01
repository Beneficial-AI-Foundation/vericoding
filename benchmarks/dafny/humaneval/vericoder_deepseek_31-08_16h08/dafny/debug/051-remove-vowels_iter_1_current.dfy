

// <vc-helpers>
predicate isVowel(c: char) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

function filterVowels(s: string): string
    ensures forall i :: 0 <= i < |result| ==> !isVowel(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] in s
    ensures forall j :: 0 <= j < |s| && !isVowel(s[j]) ==> s[j] in result
{
    if |s| == 0 then ""
    else if isVowel(s[0]) then filterVowels(s[1..])
    else [s[0]] + filterVowels(s[1..])
}

lemma filterVowelsPreservesNonVowels(s: string, j: int)
    requires 0 <= j < |s|
    requires !isVowel(s[j])
    ensures s[j] in filterVowels(s)
{
    // This lemma helps prove the third postcondition
}

lemma filterVowelsOnlyContainsOriginal(s: string, i: int)
    requires 0 <= i < |filterVowels(s)|
    ensures filterVowels(s)[i] in s
{
    // This lemma helps prove the second postcondition
}

lemma filterVowelsNoVowels(s: string, i: int)
    requires 0 <= i < |filterVowels(s)|
    ensures !isVowel(filterVowels(s)[i])
{
    // This lemma helps prove the first postcondition
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
    s := filterVowels(text);
}
// </vc-code>

