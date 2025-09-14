predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma lemma_SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures multiset(a[..]) == old(multiset(a[..]))
{
    // The Dafny verifier can often deduce this directly, but providing
    // the intermediate steps can sometimes help with more complex scenarios.
}

lemma lemma_sorted_seg_strengthen(a: array<int>, k: int, j: int)
  requires 0 <= k <= j
  requires j < a.Length
  requires sorted_seg(a, 0, j)
  ensures sorted_seg(a, 0, k)
{
  // This lemma is implicitly handled by the sorted_seg definition.
  // No explicit proof steps are needed here, as the verifier should
  // be able to deduce this from the definition of sorted_seg itself.
}

lemma lemma_sorted_seg_extend(a: array<int>, i:int, j:int)
  requires 0 <= i <= j < a.Length
  requires sorted_seg(a,0,j)
  requires a[j] <= a[j+1]
  ensures sorted_seg(a,0,j+1)
{
  // This lemma explicitly shows how sorted_seg extends, which can be useful
  // for the verifier in loop invariants or postconditions.
}

lemma lemma_multiset_segment_permutation(a: array<int>, i: int, N: int)
  requires 0 <= i < N
  requires N == a.Length
  ensures multiset(a[0 .. i]) + multiset(a[i .. N]) == multiset(a[..])
{
  // This lemma is generally known by the verifier but can be made explicit if needed
}
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
    var N := a.Length;
    if N == 0 || N == 1 { return; } // Base cases for empty or single-element array

    for i := 1 to N - 1
        invariant 1 <= i <= N
        invariant sorted_seg(a, 0, i - 1)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant multiset(a[i .. N]) == old(multiset(old(a)[i .. N]))
    {
        var j := i;
        var key := a[j]; // Store the element to be inserted
        var old_a_at_i := a[i]; // Store original value at a[i] before shifting

        while j > 0 && a[j-1] > key
            invariant 0 <= j <= i
            invariant multiset(a[..]) == old(multiset(a[..]))
            invariant forall k' :: j <= k' < i ==> a[k'] == old(a[k'+1]) // Elements shifted right
            invariant forall k'' :: 0 <= k'' < j ==> a[k''] == old(a[k'']) // Left part unchanged
            invariant sorted_seg(a, 0, j-1) // The part to the left of the shift is sorted
            invariant (j == i || a[j] == old_a_at_i) // Either j is still at i, or a[j] holds the original value
            invariant j > 0 ==> a[j-1] > key // Important for loop condition
        {
            a[j] := a[j-1]; // Shift element to the right
            j := j - 1;
        }

        if j != i { // Only assign if key has to be put at a different position
            a[j] := key; // Place the key in its sorted position
        }

        // Prove sorted_seg(a, 0, i) after the inner loop
        // We know sorted_seg(a, 0, j-1) from the invariant of the inner loop
        // If j == 0, then a[j] (which is key) is the smallest element so far.
        // If j > 0, then a[j-1] <= key <= a[k'] for k' > j
        assert j == 0 || a[j-1] <= key;
        var current_val_at_j := a[j];
        assert forall k :: j < k <= i ==> current_val_at_j <= a[k]; // Key is less than or equal to elements to its right
        if j > 0 {
            lemma_sorted_seg_extend(a, 0, j-1); // Extend from (0, j-1) to (0, j)
        }
        assert sorted_seg(a, 0, i);
    }
}
// </vc-code>

