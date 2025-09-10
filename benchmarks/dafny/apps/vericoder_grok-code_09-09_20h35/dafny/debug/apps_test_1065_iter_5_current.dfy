predicate ValidInput(n: int, k: int, M: int, D: int) {
    2 <= n && 2 <= k <= n && 1 <= M <= n && 1 <= D <= n && M * D * k >= n
}

function CandiesUsed(x: int, d: int, k: int): int {
    x * ((d - 1) * k + 1)
}

predicate ValidDistribution(x: int, d: int, n: int, k: int, M: int, D: int) {
    1 <= x <= M && 1 <= d <= D && CandiesUsed(x, d, k) <= n
}

function Person1Candies(x: int, d: int): int {
    x * d
}

// <vc-helpers>
function MaxForD(d: int, n: int, k: int, M: int, D: int): int 
    requires 1 <= d <= D && ValidInput(n, k, M, D) 
{
    var denom := (d - 1) * k + 1;
    var maxx := if M < (n / denom) then M else n / denom;
    maxx * d
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, M: int, D: int) returns (result: int)
    requires ValidInput(n, k, M, D)
    ensures result >= 0
    ensures result <= M * D
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= result
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == result
// </vc-spec>
// <vc-code>
{
    var current_max := 0;
    var found := false;
    var xch := 0;
    var dch := 0;
    var dd := D;
    while dd >= 1 
        invariant current_max <= M * D
        invariant forall d' :: dd < d' <= D ==> MaxForD(d', n, k, M, D) <= current_max
        decreases dd
    {
        var denom := (dd - 1) * k + 1;
        var maxx := if M < (n / denom) then M else n / denom;
        var cand := maxx * dd;
        if cand > current_max {
            current_max := cand;
            found := true;
            xch := maxx;
            dch := dd;
        }
        dd := dd - 1;
    }
    result := current_max;
}
// </vc-code>

