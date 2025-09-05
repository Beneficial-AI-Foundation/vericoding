This verification task involves removing all vowels (both lowercase and uppercase) from a given string and returning the resulting string. Vowels are defined as the characters: a, e, i, o, u, A, E, I, O, U. The implementation must preserve the order of non-vowel characters and ensure the result contains only characters from the original string that are not vowels.

// ======= TASK =======
// Given a string, remove all vowels (both lowercase and uppercase) and return the resulting string.
// Vowels are defined as: a, e, i, o, u, A, E, I, O, U

// ======= SPEC REQUIREMENTS =======
predicate IsVowel(c: char) {
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

predicate ValidResult(text: string, result: string) {
    && |result| <= |text|
    && (forall i :: 0 <= i < |result| ==> !IsVowel(result[i]))
    && (forall i, j :: 0 <= i < j < |result| ==> 
        (exists k, l :: 0 <= k < l < |text| && text[k] == result[i] && text[l] == result[j] &&
        !IsVowel(text[k]) && !IsVowel(text[l])))
    && ((forall i :: 0 <= i < |text| ==> IsVowel(text[i])) ==> result == "")
    && (forall i :: 0 <= i < |text| && !IsVowel(text[i]) ==> text[i] in result)
    && (forall c :: c in result ==> c in text && !IsVowel(c))
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method remove_vowels(text: string) returns (result: string)
    ensures ValidResult(text, result)
{
    var vowels := {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'};
    var filtered := "";

    var i := 0;
    while i < |text|
        invariant 0 <= i <= |text|
        invariant |filtered| <= i
        invariant forall j :: 0 <= j < |filtered| ==> !IsVowel(filtered[j])
        invariant forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in filtered
        invariant forall c :: c in filtered ==> c in text[0..i] && !IsVowel(c)
        invariant forall j, k :: 0 <= j < k < |filtered| ==> 
            (exists m, n :: 0 <= m < n < i && text[m] == filtered[j] && text[n] == filtered[k] &&
            !IsVowel(text[m]) && !IsVowel(text[n]))
        invariant (forall j :: 0 <= j < i ==> IsVowel(text[j])) ==> filtered == ""
    {
        var c := text[i];
        if !(c in vowels) {
            filtered := filtered + [c];
        }
        i := i + 1;
    }

    result := filtered;
}
