predicate ValidInput(n: int) {
    1 <= n <= 1998
}

function ExpectedResult(n: int): string
    requires ValidInput(n)
{
    if n < 1000 then "ABC" else "ABD"
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
// </vc-spec>
// <vc-code>
{
    if n < 1000 {
        result := "ABC";
    } else {
        result := "ABD";
    }
}
// </vc-code>

