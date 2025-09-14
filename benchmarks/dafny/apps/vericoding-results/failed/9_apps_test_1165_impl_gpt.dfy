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
lemma AllQueriesBoundsIndex(n: int, queries: seq<(int, int, int)>)
  requires forall q :: q in queries ==> 1 <= q.0 <= q.1 <= n
  ensures forall i :: 0 <= i < |queries| ==> 1 <= queries[i].0 <= queries[i].1 <= n
{
  assert forall i :: 0 <= i < |queries| ==> 1 <= queries[i].0 <= queries[i].1 <= n by {
    // queries[i] is an element of queries
    assert 0 <= i < |queries|;
    assert exists j :: 0 <= j < |queries| && queries[j] == queries[i];
    assert queries[i] in queries;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  AllQueriesBoundsIndex(n, queries);
  while i < m
    invariant 0 <= i <= m
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> (
      var l, r, x := queries[k].0, queries[k].1, queries[k].2;
      (res[k] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
      (res[k] != -1 ==> l <= res[k] <= r && 0 <= res[k]-1 < |A| && A[res[k]-1] != x)
    )
    decreases m - i
  {
    var l := queries[i].0;
    var r := queries[i].1;
    var x := queries[i].2;
    assert 1 <= l <= r <= n;
    assert |A| == n;

    var t := l;
    while t <= r && A[t-1] == x
      invariant l <= t <= r + 1
      invariant 1 <= l <= r <= |A|
      invariant forall j :: l <= j < t ==> 0 <= j-1 < |A| && A[j-1] == x
      decreases r - t + 1
    {
      t := t + 1;
// </vc-code>

