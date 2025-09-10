predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    if r < n - 1 {
        return r * (r + 1) / 2;
    } else if r == n - 1 {
        return (n - 1) * n / 2;
    } else {
        return (n - 1) * n / 2 + 1;
    }
}
// </vc-code>

