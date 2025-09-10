predicate ValidInput(word: string)
{
  |word| > 0 && forall i :: 0 <= i < |word| ==> ('a' <= word[i] <= 'z') || ('A' <= word[i] <= 'Z')
}

predicate CorrectCapitalization(input: string, output: string)
  requires ValidInput(input)
{
  |output| == |input| &&
  ('A' <= output[0] <= 'Z') &&
  (('a' <= input[0] <= 'z') ==> ('A' <= output[0] <= 'Z')) &&
  (('A' <= input[0] <= 'Z') ==> (output[0] == input[0])) &&
  forall i :: 1 <= i < |input| ==> output[i] == input[i]
}

// <vc-helpers>
function CapitalizeFirst(word: string): string
  requires ValidInput(word)
  ensures ValidInput(CapitalizeFirst(word))
  ensures CorrectCapitalization(word, CapitalizeFirst(word))
{
  if 'a' <= word[0] <= 'z' then
    [word[0] - 'a' + 'A'] + word[1..]
  else
    word
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var result := CapitalizeFirst(word);
  return result;
}
// </vc-code>

