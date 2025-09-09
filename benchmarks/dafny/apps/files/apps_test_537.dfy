Given n students and a ratio k, distribute awards (diplomas and certificates) to maximize 
the number of winners while following constraints: certificates = k × diplomas, 
total winners ≤ n/2. Output the number of diplomas, certificates, and non-winners.

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

method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == OptimalDiplomas(n, k)
{
    var p := (n / 2) / (k + 1);
    var g := p * k;
    var o := n - p - g;
    result := [p, g, o];
}
