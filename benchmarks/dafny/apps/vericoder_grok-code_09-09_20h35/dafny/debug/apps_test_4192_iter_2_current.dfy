predicate ValidInput(D: int, T: int, S: int)
{
    1 <= D <= 10000 && 1 <= T <= 10000 && 1 <= S <= 10000
}

predicate CanTravel(D: int, T: int, S: int)
{
    D <= T * S
}

// <vc-helpers>
// No changes needed in helpers to fix the compilation error; the issue is solely in wrapping the method body.
// </vc-helpers>

// <vc-spec>
method solve(D: int, T: int, S: int) returns (result: string)
    requires ValidInput(D, T, S)
    ensures CanTravel(D, T, S) ==> result == "Yes"
    ensures !CanTravel(D, T, S) ==> result == "No"
// </vc-spec>
// <vc-code>
{
    if D <= T * S {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

