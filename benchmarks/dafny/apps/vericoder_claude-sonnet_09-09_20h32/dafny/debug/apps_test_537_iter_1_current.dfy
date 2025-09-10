predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 0 && k + 1 > 0
}

predicate ValidOutput(result: seq<int>, n: int, k: int) {
    |result| == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

function OptimalDiplomas(n: int, k: int): int
    requires ValidInput(n, k)
{
    (n / 2) / (k + 1)
}

// <vc-helpers>
lemma DivisionProperties(n: int, k: int)
    requires ValidInput(n, k)
    ensures OptimalDiplomas(n, k) >= 0
    ensures OptimalDiplomas(n, k) * k >= 0
    ensures OptimalDiplomas(n, k) + OptimalDiplomas(n, k) * k <= n / 2
    ensures OptimalDiplomas(n, k) * (k + 1) <= n / 2
{
    var optimal := OptimalDiplomas(n, k);
    assert optimal >= 0;
    assert optimal * k >= 0;
    assert optimal == (n / 2) / (k + 1);
    assert optimal * (k + 1) <= n / 2;
    assert optimal + optimal * k == optimal * (k + 1);
}

lemma RemainderCalculation(n: int, k: int)
    requires ValidInput(n, k)
    ensures n - OptimalDiplomas(n, k) - OptimalDiplomas(n, k) * k >= 0
{
    var optimal := OptimalDiplomas(n, k);
    DivisionProperties(n, k);
    assert optimal + optimal * k <= n / 2;
    assert n / 2 <= n;
    assert optimal + optimal * k <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == OptimalDiplomas(n, k)
// </vc-spec>
// <vc-code>
{
    var first := OptimalDiplomas(n, k);
    var second := first * k;
    var third := n - first - second;
    
    DivisionProperties(n, k);
    RemainderCalculation(n, k);
    
    result := [first, second, third];
}
// </vc-code>

