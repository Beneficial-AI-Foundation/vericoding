// <vc-preamble>
predicate ValidInput(n: int, v: int) {
    2 <= n <= 100 && 1 <= v <= 100
}

function MinCost(n: int, v: int): int
    requires ValidInput(n, v)
{
    var req := n - 1;
    if req <= v then
        req
    else
        var remaining := req - v;
        v + remaining * (remaining + 3) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The helpers section was empty and no helpers were necessary for the current task. */
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int) returns (result: int)
    requires ValidInput(n, v)
    ensures result == MinCost(n, v)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): The previous attempt had a compilation error. Removed unnecessary variable redeclaration and fixed the `if` statement to correctly assign `result` based on the `MinCost` function's logic. */
{
    var req := n - 1;
    if req <= v {
        result := req;
    } else {
        var remaining := req - v;
        result := v + remaining * (remaining + 3) / 2;
    }
}
// </vc-code>
