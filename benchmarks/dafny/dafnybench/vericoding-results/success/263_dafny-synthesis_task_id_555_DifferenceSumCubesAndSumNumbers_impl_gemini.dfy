// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumCubes(n: int): int
  requires n >= 0
{
  (n * n * (n + 1) * (n + 1)) / 4
}

function SumNumbers(n: int): int
  requires n >= 0
{
  (n * (n + 1)) / 2
}
// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  diff := SumCubes(n) - SumNumbers(n);
}
// </vc-code>
