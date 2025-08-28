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
lemma SortedImpliesRange(a: array<int>, lo: nat, hi: nat)
  requires isSorted(a)
  requires lo <= hi < a.Length
  ensures forall i: nat, j: nat :: lo <= i <= j <= hi ==> a[i] <= a[j]
{
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
method BinSearch(a: array<int>, K: int) returns (b: bool)
  requires isSorted(a)
  ensures b == exists i: nat :: i < a.Length && a[i] == K
{
  if a.Length == 0 {
    return false;
  }

  var lo: nat := 0;
  var hi: int := a.Length - 1;

  while lo <= hi
    invariant 0 <= lo <= a.Length
    invariant hi < a.Length ==> 0 <= hi <= a.Length - 1
    invariant hi >= a.Length ==> hi == a.Length - 1
    invariant forall i: nat :: i < lo ==> a[i] < K
    invariant forall i: nat :: hi < i < a.Length ==> a[i] > K
  {
    var mid: nat := lo + (hi - lo) / 2;
    if a[mid] == K {
      return true;
    } else if a[mid] < K {
      lo := mid + 1;
    } else {
      hi := mid - 1;
    }
  }
  return false;
}
// </vc-code>
