predicate ValidInput(x: int, a: int)
{
    0 <= x <= 9 && 0 <= a <= 9
}

predicate CorrectOutput(x: int, a: int, result: int)
{
    result == (if x < a then 0 else 10)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Solve(x: int, a: int) returns (result: int)
    requires ValidInput(x, a)
    ensures CorrectOutput(x, a, result)
// </vc-spec>
// <vc-code>
{
    if x < a {
        result := 0;
    } else {
        result := 10;
    }
}
// </vc-code>

