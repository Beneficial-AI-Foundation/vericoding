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

function SumWindow(powers: seq<int>, k: int, start: int, endIndex: int): int
  requires 0 <= start < k
  requires 0 <= endIndex <= |powers|
  requires endIndex % k == start % k
  decreases endIndex
{
  if endIndex <= start then 0
  else SumWindow(powers, k, start, endIndex - k) + powers[endIndex - k]
}

function MaxSumWindow(powers: seq<int>, k: int, start: int): int
  requires ValidInput(|powers|, k, powers)
  requires 0 <= start < k
{
  SumWindow(powers, k, start, |powers|)
}

ghost function MaxSumWindowDef(powers: seq<int>, k: int, start: int): int
  requires ValidInput(|powers|, k, powers)
  requires 0 <= start < k
  ensures MaxSumWindow(powers, k, start) == SumWindow(powers, k, start, |powers|)
{
  MaxSumWindow(powers, k, start)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, powers: seq<int>) returns (result: int)
    requires ValidInput(n, k, powers)
    ensures IsOptimalStartingTask(result, n, k, powers)
// </vc-spec>
// <vc-code>
{
  var minSum : int := SumWindow(powers, k, 0, |powers|);
  result := 1;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> MaxSumWindow(powers, k, j) >= minSum
    invariant minSum == MaxSumWindow(powers, k, result-1) && result >= 1 && result <= k
  {
    var currentSum := MaxSumWindow(powers, k, i);
    if currentSum < minSum {
      minSum := currentSum;
      result := i + 1;
    } else if currentSum == minSum {
      if i + 1 < result {
        result := i + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>

