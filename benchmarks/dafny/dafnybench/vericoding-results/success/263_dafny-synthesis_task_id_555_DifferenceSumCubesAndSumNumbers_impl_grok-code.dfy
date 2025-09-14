

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  var sum_cubes := n * n * (n + 1) * (n + 1) / 4;
  var sum_nums := n * (n + 1) / 2;
  return sum_cubes - sum_nums;
}
// </vc-code>

