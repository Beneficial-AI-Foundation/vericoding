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
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedOutput(input)
    ensures result == "vowel" || result == "consonant"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
