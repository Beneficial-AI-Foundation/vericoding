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
lemma OptimalDiplomasProperty(n: int, k: int)
    requires ValidInput(n, k)
    ensures OptimalDiplomas(n, k) * (k + 1) <= n / 2
{
    var d := OptimalDiplomas(n, k);
    assert d == (n / 2) / (k + 1);
    // Integer division property: (a / b) * b <= a for positive b
    assert d * (k + 1) <= n / 2;
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
    var diplomas := OptimalDiplomas(n, k);
    var certificates := diplomas * k;
    var participants := n - diplomas - certificates;
    
    OptimalDiplomasProperty(n, k);
    
    result := [diplomas, certificates, participants];
}
// </vc-code>

