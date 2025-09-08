Given a functional directed graph where each vertex i has exactly one outgoing edge
to vertex f[i] with weight w[i], find for each starting vertex the sum and minimum
weight of all edges on a path of exactly k edges.

predicate ValidGraph(n: int, f: seq<int>, w: seq<int>)
{
  n > 0 && |f| == n && |w| == n &&
  (forall i :: 0 <= i < n ==> 0 <= f[i] < n) &&
  (forall i :: 0 <= i < n ==> w[i] >= 0)
}

predicate ValidResult(n: int, sums: seq<int>, mins: seq<int>)
{
  |sums| == n && |mins| == n &&
  forall i :: 0 <= i < n ==> sums[i] >= 0 && mins[i] >= 0
}

function PathSum(start: int, k: int, f: seq<int>, w: seq<int>): int
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k >= 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  decreases k
{
  if k == 0 then 0
  else w[start] + PathSum(f[start], k - 1, f, w)
}

function PathMin(start: int, k: int, f: seq<int>, w: seq<int>): int
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k > 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  decreases k
{
  if k == 1 then w[start]
  else
    var nextMin := PathMin(f[start], k - 1, f, w);
    if w[start] <= nextMin then w[start] else nextMin
}

method ComputePathMetrics(start: int, k: int, f: seq<int>, w: seq<int>) returns (sum: int, min: int)
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k > 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  ensures sum >= 0 && min >= 0
{
  var current := start;
  var steps := 0;
  sum := 0;
  min := w[current];

  while steps < k
    invariant 0 <= steps <= k
    invariant 0 <= current < |f|
    invariant sum >= 0
    invariant min >= 0
  {
    sum := sum + w[current];
    if w[current] < min {
      min := w[current];
    }
    current := f[current];
    steps := steps + 1;
  }
}

method SolveGraph(n: int, k: int, f: seq<int>, w: seq<int>) returns (sums: seq<int>, mins: seq<int>)
  requires ValidGraph(n, f, w)
  requires k > 0
  ensures ValidResult(n, sums, mins)
{
  sums := [];
  mins := [];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sums| == i && |mins| == i
    invariant forall j :: 0 <= j < i ==> sums[j] >= 0 && mins[j] >= 0
    invariant ValidGraph(n, f, w)
  {
    assert |f| == n && |w| == n;
    assert forall j :: 0 <= j < |f| ==> 0 <= f[j] < |f|;
    assert forall j :: 0 <= j < |w| ==> w[j] >= 0;
    var sum, min := ComputePathMetrics(i, k, f, w);
    sums := sums + [sum];
    mins := mins + [min];
    i := i + 1;
  }
}
