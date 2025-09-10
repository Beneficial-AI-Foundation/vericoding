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
{
  var l := queries[k].0;
  var r := queries[k].1;
  var x := queries[k].2;
  (resArr[k] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
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
    var found := false;
    var ansLocal := -1;
    while j <= r && !found
      invariant l <= j <= r + 1
      invariant 1 <= l <= r <= n
      invariant !found ==> (forall t :: l <= t < j ==> A[t-1] == x)
      invariant ansLocal == -1 || (l <= ansLocal <= r && 0 <= ansLocal-1 < |A| && A[ansLocal-1] != x)
      decreases r - j + 1
    {
      if A[j-1] != x {
        resArr[i] := j;
        ansLocal := j;
        assert (resArr[i] != -1 ==> l <= resArr[i] <= r && 0 <= resArr[i]-1 < |A| && A[resArr[i]-1] != x);
        found := true;
      } else {
        j := j + 1;
      }
    }

    if !found {
      // From the loop invariants we know j == r+1 and all positions l..r equal x
      assert j == r + 1;
      resArr[i] := -1;
      assert (resArr[i] == -1 ==> (forall t :: l <= t <= r ==> 0 <= t-1 < |A| && A[t-1] == x));
      assert IndexOk(A, queries, resArr, i);
    } else {
      // index i was set to some ansLocal with A[ansLocal-1] != x
      assert ansLocal != -1;
      // we also set resArr[i] to that value, so the property holds for index i
      assert IndexOk(A, queries, resArr, i);
    }

    i := i + 1;
  }

  return resArr[..];
}
// </vc-code>

