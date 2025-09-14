

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    var sumCubes := (n * n * (n + 1) * (n + 1)) / 4;
    var sumNumbers := (n * (n + 1)) / 2;
    diff := sumCubes - sumNumbers;
}
// </vc-code>

