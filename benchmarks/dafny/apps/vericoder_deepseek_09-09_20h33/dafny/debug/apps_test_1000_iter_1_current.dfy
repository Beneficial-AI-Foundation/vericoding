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

// <vc-helpers>
lemma MinCostFormula(n: int, v: int)
    requires ValidInput(n, v)
    ensures MinCost(n, v) == if n - 1 <= v then n - 1 else v + ((n - v) * (n - v + 1)) / 2 - 1
{
    var req := n - 1;
    if req <= v {
        // Trivial case: direct calculation
    } else {
        var remaining := req - v;
        // remaining * (remaining + 3) / 2 = (remaining² + 3remaining)/2
        // = (remaining(remaining + 1))/2 + remaining
        calc {
            v + remaining * (remaining + 3) / 2;
            v + (remaining * (remaining + 1) + 2 * remaining) / 2;
            v + (remaining * (remaining + 1)) / 2 + remaining;
            v + ((n - v - 1) * (n - v)) / 2 + (n - v - 1);
            v + ((n - v) * (n - v + 1)) / 2 - 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int) returns (result: int)
    requires ValidInput(n, v)
    ensures result == MinCost(n, v)
// </vc-spec>
// <vc-code>
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

