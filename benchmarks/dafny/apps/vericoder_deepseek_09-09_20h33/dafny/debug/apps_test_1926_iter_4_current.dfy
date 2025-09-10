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
lemma CountViolationsForKZero(a: seq<int>, n: int, k: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures CountViolationsForK(a, n, k) >= 0
{
}

lemma CountViolationsForKCorrect(a: seq<int>, n: int, k: int, violations: int)
  requires n >= 2 && |a| == n && 1 <= k <= n - 1
  ensures violations == CountViolationsForK(a, n, k) <==> 
    violations == |set i | 2 <= i <= n && 
      var parent_idx := (i + k - 2) / k;
      parent_idx >= 1 && a[i-1] < a[parent_idx-1]|
{
}

function seqFromArray<T>(arr: array<T>) : seq<T>
  reads arr
  requires arr != null
  ensures |seqFromArray(arr)| == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> seqFromArray(arr)[i] == arr[i]
{
  if arr.Length == 0 then [] else
    var s : seq<T> := [];
    var idx := 0;
    while idx < arr.Length
      invariant 0 <= idx <= arr.Length
      invariant |s| == idx
      invariant forall i :: 0 <= i < idx ==> s[i] == arr[i]
    {
      s := s + [arr[idx]];
      idx := idx + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, a)
  ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
  var res := new int[n-1];
  var k: int := 1;
  while k <= n - 1
    invariant 1 <= k <= n
    invariant res.Length == n - 1
    invariant forall j :: 0 <= j < k-1 ==> res[j] == CountViolationsForK(a, n, j+1)
    invariant forall j :: 0 <= j < res.Length ==> res[j] >= 0
  {
    var count := 0;
    var i: int := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant count == |set j | 2 <= j < i && 
        var parent_idx := (j + k - 2) / k;
        parent_idx >= 1 && a[j-1] < a[parent_idx-1]|
    {
      var parent_idx := (i + k - 2) / k;
      if parent_idx >= 1 && a[i-1] < a[parent_idx-1] {
        count := count + 1;
      }
      i := i + 1;
    }
    res[k-1] := count;
    k := k + 1;
  }
  result := seqFromArray(res);
}
// </vc-code>

