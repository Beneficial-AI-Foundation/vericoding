predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
lemma lemma_swap_contents_preserved(a: array<int>, i: int, j: int)
  modifies a
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

lemma lemma_sorted_between_implies_sorted_between(a: array<int>, from: nat, to: nat, k: nat)
  // reads a  // Lemmas can read all memory locations by default, no need for reads clause.
  requires a != null
  requires from <= to
  requires to <= a.Length
  requires k < to
  requires sorted_between(a, from, to)
  ensures sorted_between(a, from, k)
  ensures sorted_between(a, k, to)
{}

lemma lemma_sorted_between_transitive(a: array<int>, from: nat, mid: nat, to: nat)
  // reads a  // Lemmas can read all memory locations by default, no need for reads clause.
  requires a != null
  requires from <= mid <= to
  requires to <= a.Length
  requires sorted_between(a, from, mid)
  requires sorted_between(a, mid, to)
  ensures sorted_between(a, from, to)
{}

lemma lemma_sorted_between_strengthens(a: array<int>, from: nat, to: nat, k: nat, x: int)
  // reads a  // Lemmas can read all memory locations by default, no need for reads clause.
  requires a != null
  requires from <= to <= a.Length
  requires sorted_between(a, from, to)
  requires from <= k < to
  requires x <= a[k]
  ensures forall i :: from <= i <= k ==> x <= a[i]
{}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  for i := 0 to n - 2
    invariant 0 <= i < n
    invariant forall k :: n - 1 - i <= k < n - 1 ==> a[k] <= a[k+1] // The tail is sorted with i elements
    invariant sorted_between(a, n - 1 - i, n) // Elements from n-1-i to n-1 are sorted
    invariant multiset(old(a[..])) == multiset(a[..])
  {
    for j := 0 to n - 2 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(old(a[..])) == multiset(a[..])
      invariant forall k :: n - 1 - i <= k < n - 1 ==> a[k] <= a[k+1]
      invariant sorted_between(a, n - 1 - i, n) // Elements from n-1-i to n-1 are sorted
      invariant forall k' :: j < k' < n - 1 - i ==> a[k'] >= a[j] // Added this invariant
    {
      if a[j] > a[j+1] {
        lemma_swap_contents_preserved(a, j, j+1);
      }
    }
    assert forall k :: n - 1 - i <= k < n - 1 ==> a[k] <= a[k+1];
    assert sorted_between(a, n - 1 - i, n);
    if (i + 1 < n) {
        assert a[n - 2 - i] <= a[n - 1 - i];
    }
  }
  assert sorted(a);
}
// </vc-code>

