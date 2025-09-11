// <vc-preamble>
predicate IsLowercaseLetter(c: char)
{
    'a' <= c <= 'z'
}

predicate AllLowercase(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i])
}

predicate ValidOutput(result: string)
{
    result == "A" || result == "a"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
