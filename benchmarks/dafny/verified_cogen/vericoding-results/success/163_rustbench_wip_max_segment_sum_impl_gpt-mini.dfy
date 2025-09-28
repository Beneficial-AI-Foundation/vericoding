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
/* helper modified by LLM (iteration 4): sum zero lemma */
lemma SumZero(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures Sum(a, i, i) == 0
{
  assert Sum(a, i, i) == 0;
}

/* helper modified by LLM (iteration 4): sum extension lemma (by induction) */
lemma SumAdd(a: seq<int>, i: int, j: int)
  requires 0 <= i <= j < |a|
  ensures Sum(a, i, j+1) == Sum(a, i, j) + a[j]
  decreases j - i
{
  if i == j {
    assert Sum(a, i, j+1) == a[j] + Sum(a, i, j);
  } else {
    SumAdd(a, i, j-1);
    assert Sum(a, i, j+1) == a[j] + Sum(a, i, j);
  }
}
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
  /* code modified by LLM (iteration 4): exhaustive search for maximum segment sum with maintained invariants */
  var n := a.Length;
  var bi := 0;
  var bj := 0;
  var maxSum := 0;
  var i := 0;
  SumZero(a[..], 0);
  assert Sum(a[..], bi, bj) == maxSum;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant 0 <= bi <= bj <= n
    invariant Sum(a[..], bi, bj) == maxSum
    invariant forall k, l :: 0 <= k < i && k <= l <= n ==> Sum(a[..], k, l) <= maxSum
  {
    var j := i;
    var cur := 0;
    SumZero(a[..], i);
    assert cur == Sum(a[..], i, j);
    while j < n
      invariant i <= j <= n
      invariant cur == Sum(a[..], i, j)
      invariant 0 <= bi <= bj <= n
      invariant Sum(a[..], bi, bj) == maxSum
      invariant forall k, l :: 0 <= k < i && k <= l <= n ==> Sum(a[..], k, l) <= maxSum
      invariant forall l :: i <= l <= j ==> Sum(a[..], i, l) <= maxSum
    {
      SumAdd(a[..], i, j);
      cur := cur + a[j];
      j := j + 1;
      if cur > maxSum {
        maxSum := cur;
        bi := i;
        bj := j;
      }
    }
    i := i + 1;
  }
  p := (bi, bj);
}
// </vc-code>
