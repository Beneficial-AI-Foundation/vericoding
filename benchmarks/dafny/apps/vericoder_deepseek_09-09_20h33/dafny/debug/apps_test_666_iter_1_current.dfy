function TriangularNumber(m: int): int
    requires m >= 0
{
    m * (m + 1) / 2
}

predicate ValidInput(n: int)
{
    n >= 1
}

predicate ValidResult(n: int, result: int)
    requires ValidInput(n)
{
    result >= 1 && result <= n
}

// <vc-helpers>
lemma TriangularNumberMonotonic(m: int, k: int)
    requires m >= 0 && k >= 0
    ensures m <= k ==> TriangularNumber(m) <= TriangularNumber(k)
{
    if m <= k {
        var diff := k - m;
        assert TriangularNumber(k) == TriangularNumber(m) + (diff * (m + 1) + TriangularNumber(diff));
    }
}

lemma FindTriangularNumber(n: int) returns (m: int)
    requires n >= 1
    ensures m >= 0 && TriangularNumber(m) <= n < TriangularNumber(m + 1)
{
    m := 0;
    while TriangularNumber(m + 1) <= n
        invariant m >= 0
        invariant TriangularNumber(m) <= n
    {
        m := m + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    var m := FindTriangularNumber(n);
    result := n - TriangularNumber(m);
    if result == 0 {
        result := m;
    } else {
        result := result;
    }
}
// </vc-code>

