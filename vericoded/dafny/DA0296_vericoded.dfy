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
lemma PathSumNonNegative(start: int, k: int, f: seq<int>, w: seq<int>)
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k >= 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  ensures PathSum(start, k, f, w) >= 0
  decreases k
{
  if k == 0 {
    // Base case: PathSum returns 0
  } else {
    // Inductive case: w[start] >= 0 and recursively PathSum >= 0
    PathSumNonNegative(f[start], k - 1, f, w);
  }
}

lemma PathMinNonNegative(start: int, k: int, f: seq<int>, w: seq<int>)
  requires |f| == |w| && |f| > 0
  requires 0 <= start < |f|
  requires k > 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < |f|
  requires forall i :: 0 <= i < |w| ==> w[i] >= 0
  ensures PathMin(start, k, f, w) >= 0
  decreases k
{
  if k == 1 {
    // Base case: PathMin returns w[start] which is >= 0
  } else {
    // Inductive case: both w[start] and recursive PathMin are >= 0
    PathMinNonNegative(f[start], k - 1, f, w);
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
    invariant forall j :: 0 <= j < i ==> sums[j] == PathSum(j, k, f, w)
    invariant forall j :: 0 <= j < i ==> mins[j] == PathMin(j, k, f, w)
    invariant forall j :: 0 <= j < i ==> sums[j] >= 0
    invariant forall j :: 0 <= j < i ==> mins[j] >= 0
  {
    var sum := PathSum(i, k, f, w);
    var min := PathMin(i, k, f, w);
    
    PathSumNonNegative(i, k, f, w);
    PathMinNonNegative(i, k, f, w);
    
    sums := sums + [sum];
    mins := mins + [min];
    
    i := i + 1;
  }
}
// </vc-code>

