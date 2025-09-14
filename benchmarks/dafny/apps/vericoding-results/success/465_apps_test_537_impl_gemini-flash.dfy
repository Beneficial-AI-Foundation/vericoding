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
function Divide(a: int, b: int): int
    requires b != 0
    ensures (a >= 0 && b > 0) ==> Divide(a, b) == a / b
    ensures (a >= 0 && b > 0 && b <= 1) ==> a / b <= a
    ensures (a >= 0 && b > 1) ==> a / b <= a
{
    a / b
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
    var x0: int := (n / 2) / (k + 1);
    var x1: int := x0 * k;
    var x2: int := n - x0 - x1;

    result := [x0, x1, x2];
}
// </vc-code>

