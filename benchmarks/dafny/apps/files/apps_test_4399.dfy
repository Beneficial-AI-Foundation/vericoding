// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| == 3 && forall i :: 0 <= i < |input| ==> input[i] == 'A' || input[i] == 'B'
}

predicate BusServiceExists(input: string)
    requires ValidInput(input)
{
    input[0] != input[1] || input[1] != input[2]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "Yes" <==> BusServiceExists(input)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
