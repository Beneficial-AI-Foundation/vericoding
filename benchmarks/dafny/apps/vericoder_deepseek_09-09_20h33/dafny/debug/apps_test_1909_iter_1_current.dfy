predicate ValidInput(n: int, k: int, powers: seq<int>)
{
    n > 0 && k > 0 && k <= n && n % k == 0 && |powers| == n
}

predicate IsOptimalStartingTask(result: int, n: int, k: int, powers: seq<int>)
    requires ValidInput(n, k, powers)
{
    1 <= result <= k
}

// <vc-helpers>
lemma MinIndexLemma(a: seq<int>, b: seq<int>, i: int, j: int)
  requires 0 <= i < |a| && 0 <= j < |b|
  ensures a[i] <= b[j] ==> (exists m :: 0 <= m < |b| && a[i] <= b[m])
{}

lemma MaxLemma(a: seq<int>, b: seq<int>, i: int, j: int, m: int)
  requires 0 <= i < |a| && 0 <= j < |b| && 0 <= m < |b|
  ensures a[i] <= b[j] && b[j] <= b[m] ==> a[i] <= b[m]
{}

function MaxSumWindow(powers: seq<int>, k: int, start: int): int
  requires ValidInput(|powers|, k, powers)
  requires 0 <= start < k
{
  var sum := 0;
  var i := start;
  while i < |powers|
    invariant i % k == start % k || i >= |powers|
    invariant sum == sum + 0  // placeholder
    decreases |powers| - i
  {
    sum := sum + powers[i];
    i := i + k;
  }
  sum
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, powers: seq<int>) returns (result: int)
    requires ValidInput(n, k, powers)
    ensures IsOptimalStartingTask(result, n, k, powers)
// </vc-spec>
// <vc-code>
{
  var minSum := int.MaxValue;
  result := 1;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> MaxSumWindow(powers, k, j) >= minSum
    invariant minSum == int.MaxValue || (result >= 1 && result <= k && MaxSumWindow(powers, k, result-1) <= minSum)
  {
    var currentSum := MaxSumWindow(powers, k, i);
    if currentSum < minSum {
      minSum := currentSum;
      result := i + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

