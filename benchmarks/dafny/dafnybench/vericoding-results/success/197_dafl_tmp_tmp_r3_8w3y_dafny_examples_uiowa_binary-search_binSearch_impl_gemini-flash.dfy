///////////////////
// Binary search
///////////////////


predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}


// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1]

/* Note: the following definition of isSorted:


although equivalent to the one above is not enough for Dafny to be able 
to prove the invariants for the loop in binSearch.

The given one works because it *explicitly* states that every element 
of the input array is smaller than or equal to all later elements. 
This fact is implied by the alternative definition of isSorted given 
here (which only talks about array elements and their successors). 
However, it needs to be derived as an auxiliary lemma first, something 
that Dafny is not currently able to do automatically. 
*/

// <vc-helpers>
lemma lemma_sorted_range(a: array<int>, lo: nat, hi: nat)
  requires isSorted(a)
  requires lo <= hi < a.Length
  ensures a[lo] <= a[hi]
{
  // The isSorted predicate directly implies this.
  // No explicit proof steps are needed by Dafny, as it's a direct consequence
  // of the `forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]` clause.
}
// </vc-helpers>

// <vc-spec>
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length; // exclusive upper bound

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant isSorted(a)
    invariant (exists i:nat :: i < a.Length && a[i] == K) ==> (exists i:nat :: low <= i < high && a[i] == K)
  {
    var mid := low + (high - low) / 2;
    if a[mid] == K {
      return true;
    } else if a[mid] < K {
      low := mid + 1;
    } else { // a[mid] > K
      high := mid;
    }
  }
  return false;
}
// </vc-code>

