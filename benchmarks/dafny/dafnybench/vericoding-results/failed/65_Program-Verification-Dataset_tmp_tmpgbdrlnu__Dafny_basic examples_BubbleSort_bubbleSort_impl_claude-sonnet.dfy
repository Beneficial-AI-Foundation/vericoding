predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

// <vc-helpers>
lemma bubble_step_preserves_multiset(a: array<int>, i: int, old_seq: seq<int>)
  requires 0 <= i < a.Length - 1
  requires old_seq == a[..]
  ensures a[i] > a[i + 1] ==> 
    (var new_seq := old_seq[i := old_seq[i+1]][i+1 := old_seq[i]]; multiset(new_seq) == multiset(old_seq))
{
  if a[i] > a[i + 1] {
    var new_seq := old_seq[i := old_seq[i+1]][i+1 := old_seq[i]];
    assert multiset(new_seq) == multiset(old_seq);
  }
}

lemma swap_preserves_multiset(seq1: seq<int>, i: int, j: int)
  requires 0 <= i < |seq1| && 0 <= j < |seq1|
  ensures multiset(seq1[i := seq1[j]][j := seq1[i]]) == multiset(seq1)
{
  var swapped := seq1[i := seq1[j]][j := seq1[i]];
  assert multiset(swapped) == multiset(seq1);
}

lemma bubble_preserves_order(a: array<int>, j: int, boundary: int)
  requires 0 <= j < boundary < a.Length
  requires forall k :: boundary <= k < a.Length ==> forall m :: 0 <= m <= j ==> a[m] <= a[k]
  requires a[j] > a[j+1]
  modifies a
  ensures forall k :: boundary <= k < a.Length ==> forall m :: 0 <= m <= j+1 ==> a[m] <= a[k]
{
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant i > 0 ==> (forall k :: n - i <= k < n ==> 
      forall m :: 0 <= m < n - i ==> a[m] <= a[k])
    invariant sorted(a, n - i, n)
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: n - 1 - i <= k < n ==> 
        forall m :: 0 <= m <= j ==> a[m] <= a[k]
      invariant sorted(a, n - 1 - i, n)
    {
      if a[j] > a[j + 1] {
        swap_preserves_multiset(a[..], j, j + 1);
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

