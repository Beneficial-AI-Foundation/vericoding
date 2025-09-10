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
lemma FindFirstNotXInSegment(A: seq<int>, l: int, r: int, x: int) returns (index: int)
  requires 1 <= l <= r <= |A|
  ensures -1 <= index <= |A|
  ensures index == -1 ==> (forall j :: l <= j <= r ==> A[j-1] == x)
  ensures index != -1 ==> l <= index <= r && A[index-1] != x
  decreases r - l
{
  if l > r {
    index := -1;
  } else if A[l-1] != x {
    index := l;
  } else {
    index := FindFirstNotXInSegment(A, l+1, r, x);
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
  result := [];
  var i := 0;
  while i < |queries|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> ValidResult(A, queries[0..j], result[0..j])
  {
    var l, r, x := queries[i].0, queries[i].1, queries[i].2;
    var idx := FindFirstNotXInSegment(A, l, r, x);
    result := result + [idx];
    i := i + 1;
  }
}
// </vc-code>

