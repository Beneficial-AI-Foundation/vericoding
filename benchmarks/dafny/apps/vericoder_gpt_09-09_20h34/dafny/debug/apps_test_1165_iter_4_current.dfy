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
predicate IndexOk(A: seq<int>, queries: seq<(int, int, int)>, k: nat, v: int)
    requires k < |queries|
{
    var l, r, x := queries[k].0, queries[k].1, queries[k].2;
    (v == -1 ==> (forall j {:trigger A[j-1]} :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
    (v != -1 ==> l <= v <= r && 0 <= v-1 < |A| && A[v-1] != x)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
  var R := new int[m];
  var i := 0;
  assert |queries| == m;
  while i < m
    invariant 0 <= i <= m
    invariant i <= |queries|
    invariant R.Length == m
    invariant forall k :: 0 <= k < i ==> IndexOk(A, queries, k as nat, R[k])
    decreases m - i
  {
    var l := queries[i].0;
    var r := queries[i].1;
    var x := queries[i].2;

    assert 1 <= l <= r <= n;
    assert |A| == n;

    var j := l;
    var found := false;
    var ans := -1;

    while j <= r
      invariant l <= j <= r + 1
      invariant 1 <= l <= r <= |A|
      invariant if found then l <= ans < j && A[ans-1] != x else ans == -1
      invariant if !found then (forall t {:trigger A[t-1]} :: l <= t < j ==> 0 <= t-1 < |A| && A[t-1] == x) else true
      decreases r - j + 1
    {
      if A[j-1] != x {
        found := true;
        ans := j;
        j := r + 1;
      } else {
        j := j + 1;
      }
    }

    if found {
      R[i] := ans;
      assert l <= ans <= r;
      assert 0 <= ans - 1 < |A|;
      assert IndexOk(A, queries, i as nat, R[i]);
    } else {
      R[i] := -1;
      assert j == r + 1;
      assert IndexOk(A, queries, i as nat, R[i]);
    }

    assert forall k :: 0 <= k < i + 1 ==> (if k < i then IndexOk(A, queries, k as nat, R[k]) else IndexOk(A, queries, k as nat, R[k]));
    i := i + 1;
  }

  result := R[..];

  assert |result| == |queries|;
  assert forall k :: 0 <= k < |queries| ==> result[k] == R[k];
  assert forall k :: 0 <= k < |queries| ==> IndexOk(A, queries, k as nat, result[k]);
}
// </vc-code>

