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
predicate ValidInput(n: int, a: seq<int>)
{
  n >= 2 && |a| == n
}

function CountViolationsForK(a: seq<int>, n: int, k: int): int
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
{
  |set i | 2 <= i <= n && 
    (i + k - 2) / k >= 1 && 
    a[i-1] < a[(i + k - 2) / k - 1]|
}

predicate ValidOutput(result: seq<int>, n: int, a: seq<int>)
  requires n >= 2 && |a| == n
{
  |result| == n - 1 &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] >= 0) &&
  (forall k :: 1 <= k <= n - 1 ==> result[k-1] == CountViolationsForK(a, n, k))
}

lemma CountViolationsForK_nonnegative(a: seq<int>, n: int, k: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures CountViolationsForK(a, n, k) >= 0
{
  var s := set i | 2 <= i <= n && 
             (i + k - 2) / k >= 1 && 
             a[i-1] < a[(i + k - 2) / k - 1];
  calc {
    CountViolationsForK(a, n, k) == |s|;
    >= 0;
  }
}

lemma CountViolationsForK_upper_bound(a: seq<int>, n: int, k: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures CountViolationsForK(a, n, k) <= n - 1
{
  var s := set i | 2 <= i <= n && 
             (i + k - 2) / k >= 1 && 
             a[i-1] < a[(i + k - 2) / k - 1];
  calc {
    CountViolationsForK(a, n, k) == |s|;
    <= |set i | 2 <= i <= n|;
    <= n - 1;
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
  var arr := new int[n-1];
  for k := 1 to n - 1
    invariant 1 <= k <= n
    invariant arr.Length == n - 1
    invariant forall j :: 1 <= j < k ==> arr[j-1] >= 0 && arr[j-1] == CountViolationsForK(a, n, j)
  {
    var count := 0;
    for i := 2 to n
      invariant 2 <= i <= n + 1
      invariant count == |set j | 2 <= j < i && 
                          (j + k - 2) / k >= 1 && 
                          a[j-1] < a[(j + k - 2) / k - 1] |
    {
      var parent_idx := (i + k - 2) / k;
      if parent_idx >= 1 && a[i-1] < a[parent_idx-1] {
        count := count + 1;
      }
    }
    arr[k-1] := count;
  }
  result := arr[..];
}
// </vc-code>

