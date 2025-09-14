predicate ValidInput(n: int) {
    n >= 1
}

function MaxSum(n: int): int
    requires n >= 1
{
    n * (n - 1) / 2
}

// <vc-helpers>
lemma MaxSumFormula(n: int)
    requires n >= 1
    ensures MaxSum(n) == n * (n - 1) / 2
{
    // Dafny can prove this automatically
}

lemma SumIdentity(m: int) returns (s: int)
    requires m >= 0
    ensures s == m * (m + 1) / 2
{
    if m == 0 {
        s := 0;
    } else {
        var prev := SumIdentity(m - 1);
        s := prev + m;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxSum(n)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result == i * (i - 1) / 2
    {
        result := result + i;
        i := i + 1;
    }
}
// </vc-code>

