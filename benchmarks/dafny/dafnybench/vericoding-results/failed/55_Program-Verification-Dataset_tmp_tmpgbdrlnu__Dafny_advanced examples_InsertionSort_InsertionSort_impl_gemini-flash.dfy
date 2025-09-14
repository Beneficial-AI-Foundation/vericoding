predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
predicate is_sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

lemma sorted_split(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= a.Length
  requires is_sorted(a, i, j)
  requires is_sorted(a, j, k)
  ensures is_sorted(a, i, k)
{
  forall x, y | i <= x < y < k
    ensures a[x] <= a[y]
  {
    if y < j {
      assert is_sorted(a, i, j);
    } else if x >= j {
      assert is_sorted(a, j, k);
    } else {
      // x < j and y >= j
      // This lemma is not directly applicable for insertion sort.
      // The sorted_insert is the more specific lemma needed.
    }
  }
}

lemma sorted_insert(a: array<int>, original_a: array<int>, i: int, x: int, j: int)
  requires 0 <= j <= i < a.Length
  requires is_sorted(original_a, 0, j)
  requires is_sorted(original_a, j+1, i+1)
  requires forall k :: j+1 <= k <= i ==> x < original_a[k]
  requires forall k :: 0 <= k < j ==> a[k] == original_a[k]
  requires forall k :: j+1 <= k <= i ==> a[k] == original_a[k-1]
  requires a[j] == x
  ensures is_sorted(a, 0, i + 1)
{
  forall l, m | 0 <= l < m < i + 1
    ensures a[l] <= a[m]
  {
    if m <= j {
      assert original_a[l] <= original_a[m];
      calc {
        a[l];
        == original_a[l];
        <= original_a[m];
        == a[m];
      }
    } else if l > j {
      assert original_a[l-1] <= original_a[m-1];
      calc {
        a[l];
        == original_a[l-1];
        <= original_a[m-1];
        == a[m];
      }
    } else { // l <= j and m > j
      assert l < j || (l == j && m > j);
      if (l < j) {
        assert a[l] == original_a[l];
        calc {
          a[l];
          == original_a[l];
          // We need original_a[l] <= x. If original_a[l] is the max elem in original_a[0..j-1]
          // The critical part is that x is placed at j. All elements before j are original_a[k] for k<j,
          // and all elements after j (originally) were larger than x.
          // This specific sorted_insert property needs to refer to the exact state after the shift.
        }
      }
      // When inserting x at position j, we are placing x such that original_a[0..j-1] are <= x,
      // and x is <= the elements that were originally at original_a[j..i].
      // However, after the shift, those original_a[k] become a[k+1].
      // The invariant required is that original_a[l] <= x for l < j.
      // And for m > j, x <= original_a[m-1].
      // For this to hold, we need to know that original_a[j-1] <= x.
      // The inner loop guarantees that after shifting, j is the position where x should be inserted.
      // This means a[j-1] <= x (if j > 0) and x <= a[j] (elements shifted and x inserted).

      if j > 0 {
        assert original_a[j-1] <= x; // This is what the while loop ensures before exiting
      }
      if m > j {
        assert x <= original_a[m-1]; // This is by construction of the while loop shifting elements
      }

      if l < j { // original_a[l] <= x
        assert original_a[l] <= x;
      }
      if m == j { // l < j
        assert a[l] <= a[j];
      } else if m > j { // l <= j and m > j
        calc {
          a[l];
          (l < j) == original_a[l];
          (j > 0 && l < j) <= original_a[j-1];
          <= x;
          (m > j) <= original_a[m-1];
          == a[m];
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  for i := 1 to n
    invariant 1 <= i <= n
    invariant is_sorted(a, 0, i)
    invariant forall k :: i <= k < n ==> a[k] == old(a[k])
  {
    var j := i;
    var x := a[j];
    var old_a_i := a[i]; // Store original a[i]
    var original_prefix_a := a; // Store the array state at the start of the outer loop iteration

    while j > 0 && x < a[j - 1]
      invariant 0 < j <= i
      invariant forall k :: j < k <= i ==> a[k] == original_prefix_a[k-1]
      invariant forall k :: 0 <= k < j ==> a[k] == original_prefix_a[k]
      invariant forall k :: i < k < n ==> a[k] == old(a[k]) // The tail of the array is unchanged
      invariant is_sorted(a, 0, j) // Everything upto j is sorted
      invariant original_prefix_a[i] == old_a_i // original element remains same
      invariant x == old_a_i // x is the element originally at a[i]
      decreases j
    {
      a[j] := a[j - 1];
      j := j - 1;
    }
    a[j] := x;

    // Prove post conditions for outer loop
    // 1. sorted(a, 0, i+1)
    // We need to use the sorted_insert lemma to prove this.
    // The state we need for sorted_insert is `original_prefix_a`.
    // We split original_prefix_a into [0..j] and [j+1..i+1)
    // original_prefix_a[0..j] is sorted, and original_prefix_a[j+1..i+1) are the values that were shifted.
    // The inner loop ensured original_prefix_a[k] <= x for k < j, and original_prefix_a[k] >= x for k >= j.
    // However, the lemma requires is_sorted(original_a, 0, j) and is_sorted(original_a, j+1, i+1).

    // Let's prove the conditions for sorted_insert manually.
    assert is_sorted(original_prefix_a, 0, i); // from outer loop invariant
    assert is_sorted(a, 0, j); // This is true because of the inner loop conditions

    // Now, we need to show that:
    // original_prefix_a[0..j] is sorted: This is simply original_prefix_a[0..j] which is guaranteed as is_sorted(original_prefix_a, 0, i)
    // original_prefix_a[j+1..i+1] is sorted: This refers to the original values from the portion that was shifted.

    // Let's create an appropriate snapshot for the sorted_insert lemma.
    // `initial_a` is the array `a` at the start of the current outer loop iteration.
    // `current_a` is the array `a` just before the `a[j] := x` assignment.
    // The `sorted_insert` lemma needs to work on `original_prefix_a` (which is `initial_a`).
    
    // Predicate 1 for sorted_insert: is_sorted(initial_a, 0, j)
    assert is_sorted(original_prefix_a, 0, j); // Since original_prefix_a is sorted up to i

    // Predicate 2 for sorted_insert: is_sorted(initial_a, j+1, i+1)
    if j < i { // Only if there are elements to the right of j to check
        assert is_sorted(original_prefix_a, j+1, i+1); // Since original_prefix_a is sorted up to i
    }

    // Predicate 3 for sorted_insert: forall k :: j+1 <= k <= i ==> x < initial_a[k]
    // This is explicitly what the while loop guarantees: `x < a[j - 1]` means `x` is smaller than the element `a[j-1]` which was moved to `a[j]`.
    // After the loop, `j` is the insertion point. So `a[j-1]` (if `j>0`) or `initial_a[j-1]` is `<= x`.
    // And for any `k` such that `j <= k < i`, `initial_a[k]` was shifted to `a[k+1]`.
    // The `while` condition `x < a[j-1]` implies that for all `k` which were shifted (i.e. `initial_a[k]` where `j <= k < i`), `x < initial_a[k]`.
    forall k | j <= k < i
      ensures x < original_prefix_a[k]
    {
      if k == j {
        // If k == j, then a[j] was x, but we shifted a[j-1] into a[j].
        // At this point in the code, `j` is the final insertion point.
        // The elements `original_prefix_a[j]` through `original_prefix_a[i-1]` were shifted right.
        // We need to show that x is less than these values.
        // During the loop: `x < a[j-1]`.
        // After loop termination, `j` is the first index where `x >= a[j-1]` (if `j>0`) OR `j==0`.
        // This implies that all `original_prefix_a[k]` for `k` from `j` to `i-1` were greater than `x`.
        // Thus, `x < original_prefix_a[k]` for `j <= k < i`.
      } else {
        // k > j, this element was shifted.
      }
    }


    // Predicate 4: forall k :: 0 <= k < j ==> a[k] == initial_a[k]
    forall k | 0 <= k < j
      ensures a[k] == original_prefix_a[k]
    { // provided by inner loop invariant
    }

    // Predicate 5: forall k :: j+1 <= k <= i ==> a[k] == initial_a[k-1]
    forall k | j+1 <= k <= i
      ensures a[k] == original_prefix_a[k-1]
    { // provided by inner loop invariant
    }

    // Predicate 6: a[j] == x
    assert a[j] == x;

    sorted_insert(a, original_prefix_a, i, x, j);
    assert is_sorted(a, 0, i+1);
  }
}
// </vc-code>

