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
method processQuery(A: seq<int>, l: int, r: int, x: int) returns (res: int)
    requires 1 <= l <= r <= |A|
    ensures (res == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x))
    ensures (res != -1 ==> l <= res <= r && 0 <= res-1 < |A| && A[res-1] != x)
{
    var k := l;
    while k <= r
        invariant l <= k <= r + 1
        invariant forall j :: l <= j < k ==> 0 <= j-1 < |A| && A[j-1] == x
    {
        if A[k-1] != x {
            return k;
        }
        k := k + 1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
  var result_seq: seq<int> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant ValidInput(n, m, A, queries)
    invariant ValidResult(A, queries[..i], result_seq)
  {
    var l, r, x := queries[i].0, queries[i].1, queries[i].2;
    var res := processQuery(A, l, r, x);
    result_seq := result_seq + [res];
    i := i + 1;
  }
  return result_seq;
}
// </vc-code>

