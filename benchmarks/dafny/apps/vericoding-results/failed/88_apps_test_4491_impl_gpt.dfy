predicate ValidInput(n: int, a_1: seq<int>, a_2: seq<int>)
{
    n >= 1 &&
    |a_1| == n && |a_2| == n &&
    forall i :: 0 <= i < n ==> 1 <= a_1[i] <= 100 && 1 <= a_2[i] <= 100
}

function sum_range(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    decreases end - start
    ensures sum_range(s, start, end) >= 0
    ensures start < end ==> sum_range(s, start, end) >= end - start
    ensures start < end && (forall i :: start <= i < end ==> s[i] <= 100) ==> sum_range(s, start, end) <= (end - start) * 100
{
    if start == end then 0
    else s[start] + sum_range(s, start + 1, end)
}

predicate IsValidResult(n: int, a_1: seq<int>, a_2: seq<int>, result: int)
    requires ValidInput(n, a_1, a_2)
{
    result >= n + 1 &&
    result <= (n + 1) * 100 &&
    exists i :: 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) &&
    forall i :: 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}

// <vc-helpers>
// no changes
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
  var best_i := 0;
  var best := sum_range(a_1, 0, 1) + sum_range(a_2, 0, n);
  var k := 1;

  while k < n
    invariant ValidInput(n, a_1, a_2)
    invariant 1 <= k <= n
    invariant 0 <= best_i < k
    invariant best == sum_range(a_1, 0, best_i + 1) + sum_range(a_2, best_i, n)
    invariant forall j :: 0 <= j < k ==> best >= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
    decreases n - k
  {
    var curr := sum_range(a_1, 0, k + 1) + sum_range(a_2, k, n);
    if curr > best {
      best := curr;
      best_i := k;
    }
    k := k + 1;
  }

  result := best;

  assert k == n;
  assert 0 <= best_i < n;
  assert result == sum_range(a_1, 0, best_i + 1) + sum_range(a_2, best_i, n);
  assert forall i :: 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);

  // Lower bound: result >= n + 1
  assert 0 <= 0;
  assert 0 <= best_i + 1;
  assert best_i + 1 <= |a_1|;
  assert forall t :: 0 <= t < best_i + 1 ==> a_1[t] >= 1;

  assert 0 <= best_i;
  assert best_i <= n;
  assert n <= |a_2|;
  assert forall t :: best_i <= t < n ==> a_2[t] >= 1;

  assert sum_range(a_1, 0, best_i + 1) >= best_i + 1;
  assert sum_range(a_2, best_i, n) >= n - best_i;
  assert result >= (best_i + 1) + (n - best_i);
  assert result >= n + 1;

  // Upper bound: result <= (n + 1) * 100
  assert best_i + 1 <= n;
  assert forall t :: 0 <= t < best_i + 1 ==> a_1[t] <= 100;
  assert forall t :: best_i <= t < n ==> a_2[t] <= 100;

  assert sum_range(a_1, 0, best_i + 1) <= (best_i + 1) * 100;
  assert sum_range(a_2, best_i, n) <= (n - best_i) * 100;
  assert result <= ((best_i + 1) + (n - best_i)) * 100;
  assert result <= (n + 1) * 100;

  assert exists i :: i == best_i && 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);
}
// </vc-code>

