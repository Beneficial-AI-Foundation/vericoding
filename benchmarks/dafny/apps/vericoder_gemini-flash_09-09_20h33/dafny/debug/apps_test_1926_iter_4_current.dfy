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
function CountViolationsForK_Verified(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures CountViolationsForK_Verified(a, n, k) == CountViolationsForK(a, n, k)
{
  var count := 0;
  for i := 2 to n
    invariant 0 <= count <= n
    invariant count == |set m | 2 <= m < i && 
                          var parent_idx := (m + k - 2) / k;
                          parent_idx >= 1 && parent_idx <= n && a[m-1] < a[parent_idx-1]|
  {
    var parent_idx := (i + k - 2) / k;
    if parent_idx >= 1 && parent_idx <= n-1 && a[i-1] < a[parent_idx-1] {
      count := count + 1;
    }
  }
  return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
  var result_array: array<int>;
  result_array := new int[n - 1];

  for k := 1 to n - 1
    invariant 1 <= k <= n
    invariant forall j :: 1 <= j < k ==> result_array[j-1] == CountViolationsForK(a, n, j)
    invariant result_array.Length == n - 1
  {
    result_array[k-1] := CountViolationsForK_Verified(a, n, k);
  }
  return result_array[..];
}
// </vc-code>

