

// <vc-helpers>
lemma SumOfNumbers(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (n + 1) / 2
{
  if n == 0 {
    sum := 0;
  } else {
    var s := SumOfNumbers(n - 1);
    sum := s + n;
  }
}

lemma SumOfCubes(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * n * (n + 1) * (n + 1) / 4
{
  if n == 0 {
    sum := 0;
  } else {
    var s := SumOfCubes(n - 1);
    sum := s + n * n * n;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  diff := (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
}
// </vc-code>

