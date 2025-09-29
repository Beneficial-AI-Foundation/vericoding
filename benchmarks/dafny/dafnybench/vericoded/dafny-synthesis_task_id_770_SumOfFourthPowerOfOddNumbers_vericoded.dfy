

// <vc-helpers>
lemma SumFormula(n: int)
    requires n >= 0
    ensures n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15 ==
            if n == 0 then 0 else 
            (n - 1) * (2 * (n - 1) + 1) * (24 * (n - 1) * (n - 1) * (n - 1) - 12 * (n - 1) * (n - 1) - 14 * (n - 1) + 7) / 15 + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1)
{
    if n == 0 {
        assert 0 * (2 * 0 + 1) * (24 * 0 * 0 * 0 - 12 * 0 * 0 - 14 * 0 + 7) / 15 == 0;
    } else {
        var k := n - 1;
        var oddNum := 2 * n - 1;
        var prev := k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15;
        var curr := n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15;
        
        assert curr == prev + oddNum * oddNum * oddNum * oddNum;
    }
}
// </vc-helpers>

// <vc-spec>
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
// </vc-spec>
// <vc-code>
{
    sum := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (i - 1) * (2 * (i - 1) + 1) * (24 * (i - 1) * (i - 1) * (i - 1) - 12 * (i - 1) * (i - 1) - 14 * (i - 1) + 7) / 15
    {
        var oddNum := 2 * i - 1;
        SumFormula(i);
        sum := sum + oddNum * oddNum * oddNum * oddNum;
        i := i + 1;
    }
}
// </vc-code>

