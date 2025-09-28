// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| == 1 && 'a' <= input[0] <= 'z'
}

predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

function ExpectedOutput(input: string): string
    requires ValidInput(input)
{
    if IsVowel(input[0]) then "vowel" else "consonant"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added pre-condition to the function signature */
function ComputeExpectedOutput(input: string): string
  requires ValidInput(input)
  ensures ComputeExpectedOutput(input) == ExpectedOutput(input)
{
  if IsVowel(input[0]) then "vowel" else "consonant"
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedOutput(input)
    ensures result == "vowel" || result == "consonant"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Call the helper function and assign its result to the output */
{
  result := ComputeExpectedOutput(input);
}
// </vc-code>
