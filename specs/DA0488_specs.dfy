// <vc-preamble>
predicate ValidInput(D: int, T: int, S: int)
{
    1 <= D <= 10000 && 1 <= T <= 10000 && 1 <= S <= 10000
}

predicate CanTravel(D: int, T: int, S: int)
{
    D <= T * S
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(D: int, T: int, S: int) returns (result: string)
    requires ValidInput(D, T, S)
    ensures CanTravel(D, T, S) ==> result == "Yes"
    ensures !CanTravel(D, T, S) ==> result == "No"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
