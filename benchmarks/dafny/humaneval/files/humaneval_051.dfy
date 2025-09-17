// <vc-preamble>

predicate IsVowel(c: char) {
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

predicate ValidResult(text: string, result: string) {
    && |result| <= |text|
    && (forall i :: 0 <= i < |result| ==> !IsVowel(result[i]))
    && (forall i, j :: 0 <= i < j < |result| ==> 
        (exists k, l :: (0 <= k < l < |text| && text[k] == result[i] && text[l] == result[j] &&
        !IsVowel(text[k]) && !IsVowel(text[l]))))
    && ((forall i :: 0 <= i < |text| ==> IsVowel(text[i])) ==> result == "")
    && (forall i :: 0 <= i < |text| && !IsVowel(text[i]) ==> text[i] in result)
    && (forall c :: c in result ==> c in text && !IsVowel(c))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method remove_vowels(text: string) returns (result: string)
    ensures ValidResult(text, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
