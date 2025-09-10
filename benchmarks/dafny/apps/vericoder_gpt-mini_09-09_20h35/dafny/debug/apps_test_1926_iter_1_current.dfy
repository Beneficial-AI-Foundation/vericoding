predicate ValidInput(n: int, a: seq<int>)
{
  n >= 2 && |a| == n
}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
{
  |set i | 2 <= i <= n && 
    var parent_idx := (i + k - 2) / k;
    parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
}

predicate ValidOutput(result: seq<int>, n: int, a: seq<int>)
  requires n >= 2 && |a| == n
{
  |result| == n - 1 &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] == CountViolationsForK(a, n, k))
}

// <vc-helpers>
lemma ParentIndexBoundsAll(n: int, k: int)
  requires n >= 2 && 1 <= k <= n - 1
  ensures forall i :: 2 <= i <= n ==> 1 <= (i + k - 2) / k <= n - 1
{
  if k == 1 {
    // (i + k - 2) / k = i - 1 when k == 1
    assert forall i | 2 <= i <= n
      :: 1 <= (i + k - 2) / k <= n - 1
      by {
        var v := i;
        assert (v + k - 2) / k == v - 1;
        assert 1 <= v - 1;
        assert v - 1 <= n - 1;
      }
  } else {
    // k >= 2
    assert forall i | 2 <= i <= n
      :: 1 <= (i + k - 2) / k <= n - 1
      by {
        var v := i;
        // lower bound: numerator >= k because v >= 2
        assert v + k - 2 >= k;
        assert (v + k - 2) / k >= 1;
        // upper bound: (v + k - 2) / k <= (n + k - 2) / k
        assert v + k - 2 <= n + k - 2;
        // show (n + k - 2) / k <= n - 1
        // Since k >= 2 and k <= n - 1, we have k*(n - 1) >= 2*(n - 1)
        // and 2*(n - 1) >= n + k - 2 because n >= k
        assert k >= 2;
        assert k <= n - 1;
        assert k * (n - 1) >= 2 * (n - 1);
        assert n >= k; // from k <= n - 1
        assert 2 * (n - 1) >= n + k - 2;
        assert k * (n - 1) >= n + k - 2;
        // combine to get desired division bound
        assert (n + k - 2) / k <= n - 1;
        assert (v + k - 2) / k <= n - 1;
      }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
  var res := new int[n - 1];
  var k := 1;
  while k <= n - 1
    invariant 1 <= k <= n
    invariant forall j | 1 <= j < k :: res[j - 1] == CountViolationsForK(a, n, j)
    invariant forall j | 1 <= j < k :: res[j - 1] >= 0
  {
    // For this k, ensure parent indices are in bounds for all i
    ParentIndexBoundsAll(n, k);

    var cnt := 0;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant cnt == |set t | 2 <= t < i && a[t - 1] < a[((t + k - 2) / k) - 1]|
    {
      if a[i - 1] < a[((i + k - 2) / k) - 1] {
        cnt := cnt + 1;
      }
      i := i + 1;
    }

    // After inner loop, cnt equals CountViolationsForK for current k
    res[k - 1] := cnt;
    k := k + 1;
  }

  return res[..];
}
// </vc-code>

