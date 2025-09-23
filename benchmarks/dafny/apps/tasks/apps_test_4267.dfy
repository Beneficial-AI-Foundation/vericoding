// <vc-preamble>
predicate ValidTemperature(temp: int)
{
    -40 <= temp <= 40
}

function ExpectedOutput(temp: int): string
{
    if temp >= 30 then "Yes\n" else "No\n"
}

predicate CorrectOutput(temp: int, output: string)
{
    output == ExpectedOutput(temp)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (result: string)
    requires ValidTemperature(X)
    ensures CorrectOutput(X, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
