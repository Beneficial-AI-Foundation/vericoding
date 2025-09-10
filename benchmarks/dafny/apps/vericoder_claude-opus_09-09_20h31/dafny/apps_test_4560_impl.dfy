predicate ValidInput(n: int, a: int)
{
    1 <= n <= 10000 && 0 <= a <= 1000
}

predicate CanPayExactly(n: int, a: int)
{
    n % 500 <= a
}

predicate ValidOutput(result: string)
{
    result == "Yes" || result == "No"
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int) returns (result: string)
    requires ValidInput(n, a)
    ensures ValidOutput(result)
    ensures result == "Yes" <==> CanPayExactly(n, a)
// </vc-spec>
// <vc-code>
{
    if n % 500 <= a {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

