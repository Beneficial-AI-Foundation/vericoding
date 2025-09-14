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
lemma ExistsNatFromIndex(a: array<int>, K: int, x: int)
  requires 0 <= x < a.Length
  requires a[x] == K
  ensures exists i:nat :: i < a.Length && a[i] == K
{
  var i:nat :| i == x;
  assert i < a.Length;
  assert a[i] == K;
}
// </vc-helpers>

// <vc-spec>
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
// </vc-spec>
// <vc-code>
{
  var lo:int := 0;
  var hi:int := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i:nat :: i < lo ==> a[i] < K
    invariant forall i:nat :: hi <= i < a.Length ==> K < a[i]
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid < hi;
    if a[mid] < K {
      assert mid < a.Length;
      assert forall i:nat :: i < mid + 1 ==> a[i] < K
        by {
          forall i:nat | i < mid + 1
            ensures a[i] < K
          {
            assert i <= mid;
            assert i <= mid < a.Length;
            assert isSorted(a);
            assert a[i] <= a[mid];
            assert a[i] < K;
          }
        }
      lo := mid + 1;
    } else if a[mid] > K {
      assert forall i:nat :: mid <= i < a.Length ==> K < a[i]
        by {
          forall i:nat | mid <= i < a.Length
            ensures K < a[i]
          {
            assert isSorted(a);
            assert a[mid] <= a[i];
            assert K < a[i];
          }
        }
      hi := mid;
    } else {
      assert 0 <= mid < a.Length;
      assert a[mid] == K;
      ExistsNatFromIndex(a, K, mid);
      return true;
    }
  }
  assert lo == hi;
  assert forall i:nat :: i < a.Length ==> a[i] != K
    by {
      forall i:nat | i < a.Length
        ensures a[i] != K
      {
        if i < lo {
          assert a[i] < K;
          assert a[i] != K;
        } else {
          assert lo <= i;
          assert lo == hi;
          assert hi <= i;
          assert K < a[i];
          assert a[i] != K;
        }
      }
    }
  assert !(exists i:nat :: i < a.Length && a[i] == K);
  return false;
}
// </vc-code>

