method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function method IsPermutation<T>(s1: seq<T>, s2: seq<T>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
}

function method CountIf<T>(s: seq<T>, p: T -> bool): int
  reads s
  decreases s
{
  if s == [] then 0 else (if p(s[0]) then 1 else 0) + CountIf(s[1..], p)
}


// A helper function to swap elements in a sequence
function method Swap<T>(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  if i == j then s
  else s[0..i] + s[j] + s[i + 1 .. j] + s[i] + s[j + 1 ..]
}

predicate IsSorted<T>(s: seq<T>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i, j :: lo <= i < j < hi ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := s;

  var N := |s|;

  // Selection Sort
  for i := 0 to N - 2
    invariant 0 <= i <= N - 1
    invariant |sorted| == N
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
    invariant forall k :: i <= k < N && !p[k] ==> sorted[k] == s[k] // for remaining unsorted elements
    // The following invariant makes sure elements that aren't touched by `p` remain the same.
    // However, it's complex to reason about when elements are swapped.
    // Instead we rely on the multiset invariant and the explicit `!p[k]` condition.
    // invariant forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k] // This invariant is too strong and difficult to maintain
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l] // The "p" elements up to i-1 are sorted
    invariant forall l :: i <= l < N && p[l] ==> (forall k :: 0 <= k < i && p[k] ==> sorted[k] <= sorted[l]) // Smallest p-element from i onwards is sorted
    invariant multiset(s) == multiset(sorted)
  {
    var min_idx := i;
    for j := i + 1 to N - 1
      invariant i < j <= N
      invariant |sorted| == N
      invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k]
      invariant forall k :: i <= k < N && !p[k] ==> sorted[k] == s[k]
      invariant multiset(s) == multiset(sorted)
      invariant i <= min_idx < j
      invariant (p[min_idx] || !p[min_idx] && multiset(sorted) == multiset(s)) // Weakening for non-p elements
      invariant forall k :: i <= k < j && p[k] ==> sorted[min_idx] <= sorted[k] // min_idx holds smallest "p" element found so far
    {
      if p[j] && (p[min_idx] && (sorted[j] < sorted[min_idx]) || !p[min_idx]) {
        // If p[j] is true, and either p[min_idx] is true and we found a smaller element,
        // or p[min_idx] is false (meaning min_idx currently points to a non-p element, we should prefer a p element)
        min_idx := j;
      }
    }

    if min_idx != i {
      var current_val_at_i := sorted[i]; // Store the value at sorted[i] before swap
      var current_val_at_min_idx := sorted[min_idx]; // Store the value at sorted[min_idx] before swap

      sorted := Swap(sorted, i, min_idx);

      // Restore elements that are not part of predicate p
      // If the original s[i] or s[min_idx] (that moved to the other position)
      // was not supposed to be sorted (i.e. !p[_]), move it back if it's no longer at its original index
      // This part is tricky and perhaps not the best approach within a selection sort.

      // A key observation: if an element `x` at `s[k]` has `!p[k]`, then `sorted[k]` must be `x`.
      // The issue is, selection sort moves elements. If `s[i]` with `!p[i]` moves to `sorted[min_idx]`,
      // and `s[min_idx]` with `p[min_idx]` moves to `sorted[i]`, then `sorted[i]` is now `s[min_idx]`
      // and `sorted[min_idx]` is `s[i]`. This violates `!p[min_idx] ==> sorted[min_idx] == s[min_idx]`
      // if `min_idx` was an original "non-p" index (which it could be if e.g. min_idx=i).

      // The correct approach is that only elements `sorted[k]` where `p[k]` is true participate in sorting.
      // Other elements `sorted[k]` where `!p[k]` must remain `s[k]`.
      // This means the swap logic needs to be much more careful.

      // Let's re-evaluate the swap:
      // If !p[i], it must be s[i].
      // If !p[min_idx], it must be s[min_idx].

      // Case 1: p[i] && p[min_idx]
      // Regular swap. Both positions are sortable.

      // Case 2: p[i] && !p[min_idx]
      // min_idx points to an element that must not move. This can only happen if min_idx == i.
      // If min_idx != i, it means we found a *sortable* element at `j` which is `p[j]` and smaller than `sorted[i]`.
      // This implies that `min_idx` must eventually point to a `p` element unless all `p` elements are already sorted.
      // The inner loop condition: `p[j] && (p[min_idx] && (sorted[j] < sorted[min_idx]) || !p[min_idx])`
      // If `!p[min_idx]` is true, it means `sorted[min_idx]` is currently `s[min_idx]`, and we found `p[j]` which is smaller.
      // So `min_idx` *will* be updated to `j`. This ensures `min_idx` will point to a `p` element (if one exists).
      // So at this point, if `min_idx != i`, it must be that `p[min_idx]` is true.
      
      // So the only remaining case for `!p[min_idx]` is if `min_idx == i` and `!p[i]`.
      if !p[i] {
        //sorted[i] must be s[i]. If we found a smaller p[min_idx] (which means p[min_idx] is true due to prior logic),
        // we essentially skip sorting this spot.
        // This scenario implies that we should not be swapping `i` if `!p[i]`.
        // The outer loop `for i := 0 to N - 2`: we should only consider `i` if `p[i]` is true.
        // If `!p[i]`, then `sorted[i]` must remain `s[i]`.
      }
      else { // p[i] is true, so sorted[i] can be part of the sortable segment.
             // We know p[min_idx] is also true if `min_idx != i`.
        sorted := Swap(sorted, i, min_idx);
      }
    }
  }

  // The condition ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // This is a post-processing step if the in-place sort doesn't perfectly maintain it.
  // Although not ideal for efficiency, it's a correct way to ensure the postcondition.
  // A perfect in-place sort would only operate on elements `j` where `p[j]` is true.

  // Let's refine the sorting logic to directly maintain the `!p[i]` condition.
  // Instead of a selection sort on the whole array, only consider elements where `p` is true.

  // New Strategy:
  // 1. Extract elements `s[k]` where `p[k]` is true into a temporary sequence.
  // 2. Sort this temporary sequence.
  // 3. Reinsert the sorted elements back into `sorted` at their original `p[k]` positions.

  var p_indices: seq<int>;
  var p_values: seq<int>;

  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < |p_indices| ==> p[p_indices[k]] == true && s[p_indices[k]] == p_values[k]
    invariant forall k, l :: 0 <= k < l < |p_indices| ==> p_indices[k] < p_indices[l]
    invariant multiset(p_values) == multiset(s[k] | var k :: 0 <= k < i && p[k])
  {
    if p[i] {
      p_indices := p_indices + [i];
      p_values := p_values + [s[i]];
    }
  }

  // Sort p_values using a simple sort (e.g., selection sort)
  var sorted_p_values := p_values;
  var K := |sorted_p_values>;

  for i := 0 to K - 2
    invariant 0 <= i <= K - 1
    invariant |sorted_p_values> == K
    invariant forall k, l :: 0 <= k < l < i ==> sorted_p_values[k] <= sorted_p_values[l]
    invariant multiset(sorted_p_values) == multiset(p_values)
  {
    var min_idx_p := i;
    for j := i + 1 to K - 1
      invariant i < j <= K
      invariant |sorted_p_values> == K
      invariant i <= min_idx_p < j
      invariant forall k :: i <= k < j ==> sorted_p_values[min_idx_p] <= sorted_p_values[k]
      invariant multiset(sorted_p_values) == multiset(p_values)
    {
      if sorted_p_values[j] < sorted_p_values[min_idx_p] {
        min_idx_p := j;
      }
    }
    if min_idx_p != i {
      sorted_p_values := Swap(sorted_p_values, i, min_idx_p);
    }
  }

  // Construct the final sorted sequence
  sorted := s; // Start with a copy of s

  var current_p_idx := 0;
  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant 0 <= current_p_idx <= K
    invariant forall k :: 0 <= k < i && !p[k] ==> sorted[k] == s[k] // Non-p elements are preserved
    invariant forall k :: 0 <= k < i && p[k] ==> sorted[k] == sorted_p_values[CountIf(p_indices[0..current_p_idx], x => true)-1] // last true p element assigned correctly
    invariant forall k, l :: 0 <= k < l < current_p_idx ==> sorted_p_values[k] <= sorted_p_values[l] // p_values used are sorted
    invariant multiset(s) == multiset(sorted)
  {
    if p[i] {
      sorted := sorted[0..i] + [sorted_p_values[current_p_idx]] + sorted[i+1..];
      current_p_idx := current_p_idx + 1;
    }
  }

}
// </vc-code>

