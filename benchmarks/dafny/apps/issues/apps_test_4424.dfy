// <vc-preamble>
predicate ValidInput(k: int, x: int)
{
    1 <= k <= 100 && 1 <= x <= 100000
}

predicate CorrectResult(k: int, x: int, result: string)
{
    result == "Yes\n" <==> k * 500 >= x
}

predicate ValidOutput(result: string)
{
    result == "Yes\n" || result == "No\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(k: int, x: int) returns (result: string)
    requires ValidInput(k, x)
    ensures CorrectResult(k, x, result)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    if k * 500 >= x {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>
