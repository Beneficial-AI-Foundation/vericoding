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
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m && |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == DistinctCount(A, queries[j] - 1)
  {
    var start := queries[i] - 1;
    result := result + [DistinctCount(A, start)];
    i := i + 1;
  }
}
// </vc-code>

