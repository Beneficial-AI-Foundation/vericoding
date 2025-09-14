predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<int>)
{
    |A| == n && |queries| == m && n >= 1 && m >= 1 &&
    forall i :: 0 <= i < m ==> 1 <= queries[i] <= n
}

function DistinctCount(A: seq<int>, start: int): int
    requires 0 <= start < |A|
{
    |set j | start <= j < |A| :: A[j]|
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures |result| == m
    ensures forall i :: 0 <= i < m ==> 
        result[i] == DistinctCount(A, queries[i] - 1)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := [];
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == DistinctCount(A, queries[k] - 1)
    decreases m - i
  {
    assert 0 <= i < m;
    assert 1 <= queries[i] <= n;
    assert |A| == n;
    assert 0 <= queries[i] - 1 < |A|;
    result := result + [DistinctCount(A, queries[i] - 1)];
    i := i + 1;
  }
}
// </vc-code>

