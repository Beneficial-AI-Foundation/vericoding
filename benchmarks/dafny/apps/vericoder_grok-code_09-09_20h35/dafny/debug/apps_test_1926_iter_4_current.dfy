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
// Empty
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
  result := [];
  for k := 1 to n-1
    invariant |result| == k - 1
    invariant forall j :: 0 <= j < k - 1 ==> result[j] == CountViolationsForK(a, n, j+1)
  {
    var count := 0;
    for i := 2 to n {
      var parent_idx := (i + k - 2) / k;
      if parent_idx >= 1 && parent_idx <= n && a[i-1] < a[parent_idx-1] {
        count := count + 1;
      }
    }
    result := result + [count];
  }
  return result;
}
// </vc-code>

