// <vc-preamble>
function IsVowel(c: char) : bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
function IsConsonant(c: char) : bool
{
  ('A' <= c <= 'Z' || 'a' <= c <= 'z') && !IsVowel(c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed invalid 'reads' clause on string */
predicate IsSandwichedVowel(word: string, i: int)
{
  1 <= i < |word| - 1 &&
  IsVowel(word[i]) &&
  IsConsonant(word[i-1]) &&
  IsConsonant(word[i+1])
}
// </vc-helpers>

// <vc-spec>
method get_closest_vowel(word: string) returns (result: string)

  requires forall i :: 0 <= i < |word| ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')

  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 1 ==> exists i {:trigger word[i]} ::
        1 <= i && i + 1 < |word|
            && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
            && (forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): re-submitting code after fixing helper compilation error */
  if |word| < 3 {
    result := "";
    return;
  }

  var i := |word| - 2;
  result := "";

  while i >= 1
    invariant 0 <= i <= |word| - 2
    invariant forall j :: i < j <= |word| - 2 ==> !IsSandwichedVowel(word, j)
    invariant result == "" 
  {
    if IsSandwichedVowel(word, i) {
      result := word[i..i+1];
      return;
    }
    i := i - 1;
  }
}
// </vc-code>
