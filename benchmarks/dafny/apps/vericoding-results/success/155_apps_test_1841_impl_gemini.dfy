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
method CountDistinctFrom(A: seq<int>, start: int) returns (count: int)
    requires 0 <= start < |A|
    ensures count == DistinctCount(A, start)
{
    var seen: set<int> := {};
    var k := start;
    while k < |A|
        invariant start <= k <= |A|
        invariant seen == (set j | start <= j < k :: A[j])
    {
        seen := seen + {A[k]};
        k := k + 1;
    }
    count := |seen|;
}
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
  var result_arr := new int[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> result_arr[j] == DistinctCount(A, queries[j] - 1)
  {
    var start_index := queries[i] - 1;
    var count := CountDistinctFrom(A, start_index);
    result_arr[i] := count;
    i := i + 1;
  }
  result := result_arr[..];
}
// </vc-code>

