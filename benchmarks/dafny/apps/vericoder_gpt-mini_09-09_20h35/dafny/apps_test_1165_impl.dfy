predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>)
{
    n > 0 && m >= 0 && |A| == n && |queries| == m &&
    forall q :: q in queries ==> 1 <= q.0 <= q.1 <= n
}

predicate ValidResult(A: seq<int>, queries: seq<(int, int, int)>, result: seq<int>)
{
    |result| == |queries| &&
    forall i :: 0 <= i < |queries| ==> (
        var l, r, x := queries[i].0, queries[i].1, queries[i].2;
        (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
        (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x)
    )
}

// <vc-helpers>
predicate IndexOk(A: seq<int>, queries: seq<(int, int, int)>, resArr: array<int>, k: int)
  reads resArr
{
  0 <= k < |queries| && 0 <= k < resArr.Length &&
  var l := queries[k].0;
  var r := queries[k].1;
  var x := queries[k].2;
  (resArr[k] == -1 ==> (forall j :: {:trigger A[j-1]} l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
  (resArr[k] != -1 ==> l <= resArr[k] <= r && 0 <= resArr[k]-1 < |A| && A[resArr[k]-1] != x)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
  var resArr := new int[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant resArr.Length == m
    invariant forall k :: 0 <= k < i ==> IndexOk(A, queries, resArr, k)
    decreases m - i
  {
    var l := queries[i].0;
    var r := queries[i].1;
    var x := queries[i].2;

    var j := l;
    var ansLocal := -1;
    while j <= r
      invariant l <= j <= r + 1
      invariant 1 <= l <= r <= n
      invariant (ansLocal == -1 ==> (forall t :: {:trigger A[t-1]} l <= t < j ==> A[t-1] == x))
      invariant (ansLocal != -1 ==> l <= ansLocal <= r && 0 <= ansLocal-1 < |A| && A[ansLocal-1] != x)
      decreases r - j + 1
    {
      if A[j-1] != x {
        resArr[i] := j;
        ansLocal := j;
        j := r + 1;
      } else {
        j := j + 1;
      }
    }

    if ansLocal == -1 {
      // From the loop invariants we know j == r+1 and all positions l..r equal x
      resArr[i] := -1;
      assert (resArr[i] == -1 ==> (forall t :: {:trigger A[t-1]} l <= t <= r ==> 0 <= t-1 < |A| && A[t-1] == x));
      assert IndexOk(A, queries, resArr, i);
    } else {
      // we also set resArr[i] to that value, so the property holds for index i
      assert ansLocal != -1;
      assert IndexOk(A, queries, resArr, i);
    }

    i := i + 1;
  }

  return resArr[..];
}
// </vc-code>

