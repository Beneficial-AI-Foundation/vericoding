// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Ensured non-negativity of d2 for ValidOutput.*/
function ComputeResult(n: int, k: int): seq<int>
    requires ValidInput(n, k)
    ensures ValidOutput(ComputeResult(n, k), n, k)
    ensures ComputeResult(n, k)[0] == OptimalDiplomas(n, k)
{
    var d0 := OptimalDiplomas(n, k);
    var d1 := d0 * k;
    var d2 := n - d0 - d1;
    [d0, d1, d2]
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == OptimalDiplomas(n, k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Called the helper function to compute the result. */
{
  result := ComputeResult(n, k);
}
// </vc-code>
