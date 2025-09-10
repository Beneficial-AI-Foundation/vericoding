predicate ValidInput(n: int, k: int, M: int, D: int) {
    2 <= n && 2 <= k <= n && 1 <= M <= n && 1 <= D <= n && M * D * k >= n
}

function CandiesUsed(x: int, d: int, k: int): int {
    x * ((d - 1) * k + 1)
}

predicate ValidDistribution(x: int, d: int, n: int, k: int, M: int, D: int) {
    1 <= x <= M && 1 <= d <= D && CandiesUsed(x, d, k) <= n
}

function Person1Candies(x: int, d: int): int {
    x * d
}

// <vc-helpers>
lemma CandiesUsedNonNegative(x: int, d: int, k: int)
  requires 1 <= x && 1 <= d && 2 <= k
  ensures CandiesUsed(x, d, k) >= 0
{
}

lemma FindMaxHelper(n: int, k: int, M: int, D: int, x: int, d: int)
  requires ValidInput(n, k, M, D)
  requires 1 <= x <= M && 1 <= d <= D
  requires CandiesUsed(x, d, k) <= n
  ensures Person1Candies(x, d) <= M * D
{
}

lemma ExistsValidDistribution(n: int, k: int, M: int, D: int)
  requires ValidInput(n, k, M, D)
  ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D)
{
  var x := 1;
  var d := 1;
  assert ValidDistribution(x, d, n, k, M, D);
}

lemma MaxXAtLeastOne(n: int, k: int, M: int, D: int, d: int)
  requires ValidInput(n, k, M, D)
  requires 1 <= d <= D
  ensures ((n / ((d - 1) * k + 1)) min M) >= 1 || n < ((d - 1) * k + 1)
{
  var denominator := (d - 1) * k + 1;
  if n >= denominator {
    var candidate := n / denominator;
    var bounded := if candidate <= M then candidate else M;
    assert bounded >= 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, M: int, D: int) returns (result: int)
    requires ValidInput(n, k, M, D)
    ensures result >= 0
    ensures result <= M * D
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= result
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == result
// </vc-spec>
// <vc-code>
{
  var max_candies := 0;
  var d := D;
  while d >= 1
    invariant 0 <= d <= D
    invariant forall x': int, d': int :: d < d' <= D && ValidDistribution(x', d', n, k, M, D) ==> Person1Candies(x', d') <= max_candies
    invariant (exists x': int, d': int :: d <= d' <= D && ValidDistribution(x', d', n, k, M, D) && Person1Candies(x', d') == max_candies) || max_candies == 0
  {
    var denominator := (d - 1) * k + 1;
    var max_x := n / denominator;
    if max_x > M {
      max_x := M;
    }
    if max_x < 1 {
      d := d - 1;
      continue;
    }
    var candies := max_x * d;
    if candies > max_candies {
      max_candies := candies;
    }
    if max_x >= 1 && max_x <= M && 1 <= d <= D && CandiesUsed(max_x, d, k) <= n {
      assert ValidDistribution(max_x, d, n, k, M, D);
    }
    d := d - 1;
  }
  result := max_candies;
}
// </vc-code>

