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
lemma pivot_transitive(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  requires pivot(a, a.Length, i)
  requires pivot(a, a.Length, j)
  ensures forall u, v :: 0 <= u < i < v < a.Length ==> a[u] <= a[v]
{}

lemma sorted_implies_pivot(a: array<int>, from: int, to: int, pvt: int)
  requires 0 <= from <= pvt < to <= a.Length
  requires sorted(a, from, to)
  ensures forall u, v :: from <= u < pvt < v < to ==> a[u] <= a[v]
{}

lemma swap_preserves_multiset_seq(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
  var s' := s[i := s[j]][j := s[i]];
  assert s'[i] == s[j] && s'[j] == s[i];
  assert forall k :: 0 <= k < |s| && k != i && k != j ==> s'[k] == s[k];
}

lemma swap_maintains_pivot(a: array<int>, j: int, pvt: int, old_seq: seq<int>)
  requires 0 <= j < j+1 < pvt < a.Length
  requires |old_seq| == a.Length
  requires a[..] == old_seq[j := old_seq[j+1]][j+1 := old_seq[j]]
  requires forall u, v :: 0 <= u < pvt < v < |old_seq| ==> old_seq[u] <= old_seq[v]
  requires old_seq[j] > old_seq[j+1]  // We swapped because j > j+1
  requires forall k :: 0 <= k < j ==> old_seq[k] <= old_seq[j]  // Loop invariant before swap
  ensures pivot(a, a.Length, pvt)
{
  forall u, v | 0 <= u < pvt < v < a.Length
    ensures a[u] <= a[v]
  {
    if u == j {
      assert a[u] == old_seq[j+1];
      assert a[v] == old_seq[v];
      assert old_seq[j+1] <= old_seq[v];
    } else if u == j+1 {
      assert a[u] == old_seq[j];
      assert a[v] == old_seq[v];
      assert old_seq[j] <= old_seq[v];
    } else {
      assert a[u] == old_seq[u];
      assert a[v] == old_seq[v];
      assert old_seq[u] <= old_seq[v];
    }
  }
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
  var i := a.Length - 1;
  while i > 0
    invariant 0 <= i < a.Length
    invariant sorted(a, i, a.Length)
    invariant pivot(a, a.Length, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant sorted(a, i, a.Length)
      invariant pivot(a, a.Length, i)
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] > a[j + 1] {
        ghost var old_seq := a[..];
        ghost var old_invariant := forall k :: 0 <= k < j ==> a[k] <= a[j];
        assert old_seq[j] > old_seq[j+1];  // We're swapping because j > j+1
        
        a[j], a[j + 1] := a[j + 1], a[j];
        
        var swapped_seq := old_seq[j := old_seq[j+1]][j+1 := old_seq[j]];
        assert a[..] == swapped_seq;
        swap_preserves_multiset_seq(old_seq, j, j + 1);
        assert multiset(swapped_seq) == multiset(old_seq);
        assert multiset(a[..]) == multiset(old_seq);
        assert multiset(old_seq) == multiset(old(a[..]));
        
        if j + 1 < i {
          assert forall k :: 0 <= k < j ==> old_seq[k] <= old_seq[j];  // From loop invariant
          swap_maintains_pivot(a, j, i, old_seq);
        }
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
// </vc-code>

