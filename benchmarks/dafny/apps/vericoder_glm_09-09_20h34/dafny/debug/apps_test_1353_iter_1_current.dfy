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

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result >= 0
    ensures result == OptimalCost(n, m, a, b)
// </vc-spec>
// <vc-code>
var all_single := n * a;
    var all_multi := ((n + m - 1) / m) * b;
    var mixed := (n / m) * b + (n % m) * a;
    var temp := if all_multi < mixed then all_multi else mixed;
    result := if all_single < temp then all_single else temp;
    assert result == OptimalCost(n, m, a, b);
// </vc-code>

