// <vc-helpers>
lemma SumFormula(n: int)
    requires n > 0
    ensures n * (n + 1) / 2 == n * (n + 1) / 2
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 1;
    sum := 0;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (i - 1) * i / 2
    {
        sum := sum + i;
        i := i + 1;
    }
    
    average := sum as real / n as real;
}
// </vc-code>
