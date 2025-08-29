// <vc-helpers>
predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

predicate AllNonVowels(s: string)
{
    forall i :: 0 <= i < |s| ==> !IsVowel(s[i])
}

lemma FilterPreservesNonVowels(s: string, result: string)
    requires result == seq(i | 0 <= i < |s| && !IsVowel(s[i]) | s[i])
    ensures AllNonVowels(result)
{
    forall i | 0 <= i < |result|
        ensures !IsVowel(result[i])
    {
        assert result[i] in result;
        var j :| 0 <= j < |s| && !IsVowel(s[j]) && result[i] == s[j];
        assert !IsVowel(s[j]);
        assert result[i] == s[j];
        assert !IsVowel(result[i]);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def remove_vowels(string: str) -> string
remove_vowels is a function that takes string and returns string without vowels.
*/
// </vc-description>

// <vc-spec>
method RemoveVowels(s: string) returns (result: string)
    ensures AllNonVowels(result)
    ensures forall c :: c in result ==> c in s && !IsVowel(c)
    ensures forall i :: 0 <= i < |s| && !IsVowel(s[i]) ==> s[i] in result
// </vc-spec>
// <vc-code>
{
    result := seq(i | 0 <= i < |s| && !IsVowel(s[i]) | s[i]);
    FilterPreservesNonVowels(s, result);
}
// </vc-code>
