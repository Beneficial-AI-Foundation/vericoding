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
    ensures min(x, y) <= x
    ensures min(x, y) <= y
    ensures min(x, y) == x || min(x, y) == y
{
}

lemma OptimalCostProperties(n: int, m: int, a: int, b: int)
    requires ValidInput(n, m, a, b)
    ensures OptimalCost(n, m, a, b) >= 0
    ensures OptimalCost(n, m, a, b) <= n * a
{
    assert n >= 1 && a >= 1;
    assert n * a >= n >= 1;
}

lemma OptimalCostCorrect(n: int, m: int, a: int, b: int, allSingle: int, allMulti: int, mixed: int)
    requires ValidInput(n, m, a, b)
    requires allSingle == n * a
    requires allMulti == ((n + m - 1) / m) * b
    requires mixed == (n / m) * b + (n % m) * a
    ensures min(allSingle, min(allMulti, mixed)) == OptimalCost(n, m, a, b)
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
    
    OptimalCostCorrect(n, m, a, b, allSingle, allMulti, mixed);
    
    if allMulti < allSingle && allMulti <= mixed {
        result := allMulti;
    } else if mixed < allSingle && mixed <= allMulti {
        result := mixed;
    } else {
        result := allSingle;
    }
    
    MinProperties(allSingle, allMulti, mixed);
}
// </vc-code>

