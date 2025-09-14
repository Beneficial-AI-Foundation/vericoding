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

// <vc-helpers>
lemma PathSumPositive(start: int, k: int, f: seq<int>, w: seq<int>)
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k >= 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  ensures PathSum(start, k, f, w) >= 0
  decreases k
{
  if k > 0 {
    PathSumPositive(f[start], k - 1, f, w);
  }
}

lemma PathMinPositive(start: int, k: int, f: seq<int>, w: seq<int>)
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k > 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  ensures PathMin(start, k, f, w) >= 0
  decreases k
{
  if k > 1 {
    PathMinPositive(f[start], k - 1, f, w);
  }
}
// </vc-helpers>

// <vc-spec>
method SolveGraph(n: int, k: int, f: seq<int>, w: seq<int>) returns (sums: seq<int>, mins: seq<int>)
  requires ValidGraph(n, f, w)
  requires k > 0
  ensures ValidResult(n, sums, mins)
// </vc-spec>
// <vc-code>
{
  sums := [];
  mins := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sums| == i
    invariant |mins| == i
    invariant forall j :: 0 <= j < i ==> sums[j] >= 0 && mins[j] >= 0
  {
    var s := PathSum(i, k, f, w);
    PathSumPositive(i, k, f, w);
    sums := sums + [s];
    var m := PathMin(i, k, f, w);
    PathMinPositive(i, k, f, w);
    mins := mins + [m];
    i := i + 1;
  }
}
// </vc-code>

