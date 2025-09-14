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

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (result: string)
    requires ValidTemperature(X)
    ensures CorrectOutput(X, result)
// </vc-spec>
// <vc-code>
{
  result := if X >= 30 then "Yes\n" else "No\n";
  assert result == ExpectedOutput(X);
}
// </vc-code>

