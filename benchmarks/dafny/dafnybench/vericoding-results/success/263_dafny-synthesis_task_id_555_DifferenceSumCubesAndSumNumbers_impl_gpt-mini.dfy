

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == i * (i + 1) / 2
    decreases n - i
  {
    i := i + 1;
    s := s + i;
  }
  diff := (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
}
// </vc-code>

