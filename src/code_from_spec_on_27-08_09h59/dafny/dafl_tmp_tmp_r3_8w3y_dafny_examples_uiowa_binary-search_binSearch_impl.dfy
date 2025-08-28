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
lemma sortedProperty(a: array<int>, i: int, j: int)
  requires isSorted(a)
  requires 0 <= i <= j < a.Length
  ensures a[i] <= a[j]
{
}

lemma sortedMidProperty(a: array<int>, lo: int, hi: int, mid: int, K: int)
  requires isSorted(a)
  requires 0 <= lo <= mid < hi <= a.Length
  requires a[mid] < K
  ensures forall k :: lo <= k <= mid ==> a[k] < K
{
  forall k | lo <= k <= mid
    ensures a[k] < K
  {
    sortedProperty(a, k, mid);
  }
}

lemma sortedMidPropertyGreater(a: array<int>, lo: int, hi: int, mid: int, K: int)
  requires isSorted(a)
  requires 0 <= lo <= mid < hi <= a.Length
  requires a[mid] > K
  ensures forall k :: mid <= k < hi ==> a[k] > K
{
  forall k | mid <= k < hi
    ensures a[k] > K
  {
    sortedProperty(a, mid, k);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if a.Length == 0 {
    return false;
  }
  
  var lo := 0;
  var hi := a.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall k :: 0 <= k < lo ==> a[k] < K
    invariant forall k :: hi <= k < a.Length ==> a[k] > K
    invariant (exists i:nat :: i < a.Length && a[i] == K) <==> (exists i:nat :: lo <= i < hi && a[i] == K)
  {
    var mid := (lo + hi) / 2;
    
    if a[mid] == K {
      return true;
    } else if a[mid] < K {
      sortedMidProperty(a, lo, hi, mid, K);
      lo := mid + 1;
    } else {
      sortedMidPropertyGreater(a, lo, hi, mid, K);
      hi := mid;
    }
  }
  
  return false;
}
// </vc-code>
