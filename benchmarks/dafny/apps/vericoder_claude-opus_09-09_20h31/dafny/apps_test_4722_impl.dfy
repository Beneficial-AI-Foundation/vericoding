predicate ValidInput(A: int, B: int)
{
    1 <= A <= 100 && 1 <= B <= 100
}

predicate DistributionPossible(A: int, B: int)
{
    A % 3 == 0 || B % 3 == 0 || (A + B) % 3 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int) returns (result: string)
    requires ValidInput(A, B)
    ensures result == "Possible" <==> DistributionPossible(A, B)
    ensures result == "Possible" || result == "Impossible"
// </vc-spec>
// <vc-code>
{
    if A % 3 == 0 || B % 3 == 0 || (A + B) % 3 == 0 {
        result := "Possible";
    } else {
        result := "Impossible";
    }
}
// </vc-code>

