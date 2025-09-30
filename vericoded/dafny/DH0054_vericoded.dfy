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
function CollectNonVowels(text: string): string
/* helper modified by LLM (iteration 3): Fixed compilation error by restructuring if-else with expression-based branches */
ensures ValidResult(text, CollectNonVowels(text))
{
  if |text| == 0 then ""
  else if !IsVowel(text[0]) then [text[0]] + CollectNonVowels(text[1..])
  else CollectNonVowels(text[1..])
}
// </vc-helpers>

// <vc-spec>
method remove_vowels(text: string) returns (result: string)
    ensures ValidResult(text, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Call helper function to remove vowels and assign to result */
  result := CollectNonVowels(text);
}
// </vc-code>
