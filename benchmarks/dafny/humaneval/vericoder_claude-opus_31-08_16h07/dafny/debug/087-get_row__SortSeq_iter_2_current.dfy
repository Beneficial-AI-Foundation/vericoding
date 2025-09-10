type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
  // post-conditions-start
  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma LessTransitive(a: (int, int), b: (int, int), c: (int, int))
  requires less(a, b) && less(b, c)
  ensures less(a, c)
{
  var (x, y) := a; var (u, v) := b; var (p, q) := c;
  if x < u {
    if u < p {
      assert x < p;
    } else {
      assert u == p && v > q;
      assert x < p;
    }
  } else {
    assert x == u && y > v;
    if u < p {
      assert x < p;
    } else {
      assert u == p && v > q;
      assert x == p && y > q;
    }
  }
}

lemma LessEqTransitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b) && less_eq(b, c)
  ensures less_eq(a, c)
{
  if a == b {
    assert less_eq(a, c);
  } else if b == c {
    assert less_eq(a, c);
  } else {
    assert less(a, b) && less(b, c);
    LessTransitive(a, b, c);
    assert less(a, c);
    assert less_eq(a, c);
  }
}

lemma NotLessImpliesLessEqReverse(a: (int, int), b: (int, int))
  requires !less(a, b) && a != b
  ensures less(b, a)
{
  var (x, y) := a; var (u, v) := b;
  if x != u {
    assert u < x;
  } else {
    assert !(y > v);
    assert y < v;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall k, l :: 0 <= k < l < i ==> less_eq(sorted[k], sorted[l])
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < |sorted| ==> less_eq(sorted[k], sorted[l])
  {
    var j := i + 1;
    var minIdx := i;
    
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> less_eq(sorted[minIdx], sorted[k])
    {
      if less(sorted[j], sorted[minIdx]) {
        minIdx := j;
      }
      j := j + 1;
    }
    
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
    
    i := i + 1;
  }
}
// </vc-code>

