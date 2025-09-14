// <vc-preamble>
function Sum(a: seq<int>, s: int, t: int): int
    decreases t - s
{
    if s < 0 || s >= t || t > |a| then
        0
    else
        a[t - 1] + Sum(a, s, t - 1)
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
predicate ValidRange(s: int, t: int, n: int) { 0 <= s <= t <= n }
lemma SumEmpty(a: seq<int>, s: int)
  ensures Sum(a, s, s) == 0
{ }
// </vc-helpers>

// <vc-spec>
method MaxSegmentSum(a: array<int>, s: int, t: int) returns (p: (int, int))
    ensures
        var (i, j) := p; 0 <= i <= j <= a.Length
    ensures
        var (i, j) := p; forall k: int, l: int :: 0 <= k <= l <= a.Length ==> Sum(a[..], k, l) <= Sum(a[..], i, j)
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var sa := a[..];
  var bestI := 0;
  var bestJ := 0;
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant 0 <= bestI <= bestJ <= n
    invariant forall k: int, l: int :: 0 <= k < i && k <= l <= n ==> Sum(sa, k, l) <= Sum(sa, bestI, bestJ)
    decreases n + 1 - i
  {
    var j := i;
    while j <= n
      invariant i <= j <= n + 1
      invariant 0 <= bestI <= bestJ <= n
      invariant forall k: int, l: int :: 0 <= k < i && k <= l <= n ==> Sum(sa, k, l) <= Sum(sa, bestI, bestJ)
      invariant forall l: int :: i <= l < j ==> Sum(sa, i, l) <= Sum(sa, bestI, bestJ)
      decreases n + 1 - j
    {
      if Sum(sa, i, j) > Sum(sa, bestI, bestJ) {
        bestI := i;
        bestJ := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  p := (bestI, bestJ);
}
// </vc-code>
