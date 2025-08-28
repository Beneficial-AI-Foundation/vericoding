// By `lol sort` here, I refer to a seemingly-broken sorting algorithm,
// which actually somehow manages to work perfectly:
//
// for i in 0..n
//   for j in 0..n
//     if i < j
//       swap a[i], a[j]
//
// It is perhaps the simpliest sorting algorithm to "memorize",
// even "symmetrically beautiful" as if `i` and `j` just played highly
// similar roles. And technically it's still O(n^2) time lol...
//
// Proving its correctness is tricky (interesting) though.

// Successfully verified with [Dafny 3.3.0.31104] in about 5 seconds.



// We define "valid permutation" using multiset:

predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

// This is a swap-based sorting algorithm, so permutedness is trivial:
// note that: if i == j, the spec just says a[..] remains the same.
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{
  assume{:axiom} false;
}

// We then define "sorted" (by increasing order):
predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}


// Now, the lol sort algorithm:
// (Some invariants were tricky to find, but Dafny was smart enough otherwise)

// <vc-helpers>
lemma swap_preserves_sorted_prefix(a: seq<int>, old_a: seq<int>, i: int, j: int, k: int)
  requires 0 <= i < |a| && 0 <= j < |a| && 0 <= k <= i
  requires |a| == |old_a|
  requires a == old_a[i := old_a[j]][j := old_a[i]]
  requires forall x, y | 0 <= x <= y < k :: old_a[x] <= old_a[y]
  ensures forall x, y | 0 <= x <= y < k :: a[x] <= a[y]
{
  forall x, y | 0 <= x <= y < k ensures a[x] <= a[y] {
    assert k <= i;
    assert x < k <= i;
    assert y < k <= i;
    assert x != i && y != i;
    assert a[x] == old_a[x];
    assert a[y] == old_a[y];
    assert old_a[x] <= old_a[y];
  }
}

lemma swap_maintains_order_invariant(a: seq<int>, old_a: seq<int>, i: int, j: int, outer_i: int)
  requires 0 <= i < |a| && 0 <= j < |a| && 0 <= outer_i < |a|
  requires |a| == |old_a|
  requires a == old_a[i := old_a[j]][j := old_a[i]]
  requires forall k | 0 <= k < outer_i :: forall l | outer_i <= l < |a| :: old_a[k] <= old_a[l]
  ensures forall k | 0 <= k < outer_i :: forall l | outer_i <= l < |a| :: a[k] <= a[l]
{
  forall k | 0 <= k < outer_i ensures forall l | outer_i <= l < |a| :: a[k] <= a[l] {
    forall l | outer_i <= l < |a| ensures a[k] <= a[l] {
      assert k < outer_i <= i;
      assert l >= outer_i >= i;
      if k == i && l == j {
        assert a[k] == old_a[j];
        assert a[l] == old_a[i];
        assert old_a[k] <= old_a[l];
      } else if k == i {
        assert k < outer_i;
        assert false;
      } else if l == j {
        assert a[k] == old_a[k];
        assert a[l] == old_a[i];
        assert old_a[k] <= old_a[i];
      } else {
        assert a[k] == old_a[k];
        assert a[l] == old_a[l];
        assert old_a[k] <= old_a[l];
      }
    }
  }
}

lemma swap_property(a: seq<int>, i: int, j: int, x: int)
  requires 0 <= i < |a| && 0 <= j < |a| && 0 <= x < |a|
  requires x != i && x != j
  ensures a[i := a[j]][j := a[i]][x] == a[x]
{
}

lemma swap_maintains_inner_invariant(old_a: seq<int>, new_a: seq<int>, i: int, j: int, outer_j: int)
  requires 0 <= i < |old_a| && 0 <= j < |old_a| && 0 <= outer_j < |old_a|
  requires |new_a| == |old_a|
  requires i < j
  requires new_a == old_a[i := old_a[j]][j := old_a[i]]
  requires forall k | i <= k < outer_j :: old_a[i] <= old_a[k]
  requires old_a[i] <= old_a[j]
  ensures forall k | i <= k < outer_j + 1 :: new_a[i] <= new_a[k]
{
  forall k | i <= k < outer_j + 1 ensures new_a[i] <= new_a[k] {
    if k == j {
      assert new_a[i] == old_a[j];
      assert new_a[k] == old_a[i];
      assert old_a[i] <= old_a[j];
      assert new_a[i] <= new_a[k];
    } else if k < outer_j {
      assert new_a[i] == old_a[j];
      if k != i {
        assert new_a[k] == old_a[k];
        assert old_a[i] <= old_a[k];
        assert old_a[i] <= old_a[j];
      } else {
        assert k == i;
        assert new_a[i] == old_a[j];
        assert new_a[k] == old_a[j];
      }
    } else {
      assert k == outer_j;
      assert k < j;
      assert new_a[i] == old_a[j];
      if k != i {
        assert new_a[k] == old_a[k];
        assert old_a[i] <= old_a[k];
      } else {
        assert new_a[i] == old_a[j];
        assert new_a[k] == old_a[j];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := a.Length;
  for i := 0 to n
    invariant valid_permut(a[..], old(a[..]))
    invariant forall k, l | 0 <= k <= l < i :: a[k] <= a[l]
    invariant forall k | 0 <= k < i :: forall l | i <= l < n :: a[k] <= a[l]
  {
    for j := 0 to n
      invariant valid_permut(a[..], old(a[..]))
      invariant forall k, l | 0 <= k <= l < i :: a[k] <= a[l]
      invariant forall k | 0 <= k < i :: forall l | i <= l < n :: a[k] <= a[l]
      invariant forall k | i <= k < j :: a[i] <= a[k]
    {
      if i < j {
        var old_a := a[..];
        
        assert old_a[i] <= old_a[j];
        
        swap(a, i, j);
        
        assert a[..] == old_a[i := old_a[j]][j := old_a[i]];
        
        swap_preserves_sorted_prefix(a[..], old_a, i, j, i);
        swap_maintains_order_invariant(a[..], old_a, i, j, i);
        swap_maintains_inner_invariant(old_a, a[..], i, j, j);
        
        assert a[i] == old_a[j];
        assert a[j] == old_a[i];
      }
    }
  }
}
// </vc-code>
