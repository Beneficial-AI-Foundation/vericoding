predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

function OptimalCost(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    min(
        n * a,  // All single tickets
        min(
            ((n + m - 1) / m) * b,  // All multi-ride tickets (with potential waste)
            (n / m) * b + (n % m) * a  // Mixed: multi-ride + single for remainder
        )
    )
}

// <vc-helpers>
function min(x: int, y: int): int
{
    if x <= y then x else y
}

lemma MinProperties(x: int, y: int, z: int)
    ensures min(x, min(y, z)) == min(min(x, y), z)
    ensures min(x, y) <= x && min(x, y) <= y
    ensures min(x, y) == x || min(x, y) == y
{
}

lemma DivisionProperties(n: int, m: int)
    requires n >= 0 && m > 0
    ensures (n + m - 1) / m >= n / m
    ensures (n + m - 1) / m <= n / m + 1
    ensures n / m >= 0
    ensures n % m >= 0 && n % m < m
    ensures n == (n / m) * m + (n % m)
{
    if n < m {
        assert (n + m - 1) / m == 1;
        assert n / m == 0;
    } else {
        var q := n / m;
        var r := n % m;
        assert n == q * m + r;
        assert 0 <= r < m;
        
        if r == 0 {
            assert (n + m - 1) / m == q;
        } else {
            assert (n + m - 1) / m == q + 1;
        }
    }
}

lemma OptimalCostNonNegative(n: int, m: int, a: int, b: int)
    requires ValidInput(n, m, a, b)
    ensures OptimalCost(n, m, a, b) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result >= 0
    ensures result == OptimalCost(n, m, a, b)
// </vc-spec>
// <vc-code>
{
    var allSingle := n * a;
    var allMulti := ((n + m - 1) / m) * b;
    var mixed := (n / m) * b + (n % m) * a;
    
    result := min(allSingle, min(allMulti, mixed));
    
    OptimalCostNonNegative(n, m, a, b);
}
// </vc-code>

