predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SwapMaintains(oldSeq: seq<int>, a: array<int>, i:int, minIdx:int)
  requires a != null
  requires 0 <= i < a.Length
  requires i <= minIdx < a.Length
  requires oldSeq.Length == a.Length
  // oldSeq captures the array contents before the swap
  requires forall j,k :: 0 <= j < k < i ==> oldSeq[j] <= oldSeq[k]
  requires forall p,k :: 0 <= p < i <= k < a.Length ==> oldSeq[p] <= oldSeq[k]
  requires forall t :: i <= t < a.Length ==> oldSeq[minIdx] <= oldSeq[t]
  // the relation between oldSeq and a after the swap
  requires a[i] == oldSeq[minIdx]
  requires a[minIdx] == oldSeq[i]
  requires forall k :: 0 <= k < a.Length && k != i && k != minIdx ==> a[k] == oldSeq[k]
{
  // Prove sorted on [0..i+1)
  assert forall j,k | 0 <= j < k < i+1 {
    if k < i {
      // both indices < i : unchanged, use oldSeq sortedness
      assert a[j] == oldSeq[j];
      assert a[k] == oldSeq[k];
      assert oldSeq[j] <= oldSeq[k];
      assert a[j] <= a[k];
    } else {
      // k == i
      assert a[j] == oldSeq[j];
      assert a[k] == oldSeq[minIdx];
      // oldSeq[j] <= oldSeq[minIdx] because 0 <= j < i <= minIdx
      assert oldSeq[j] <= oldSeq[minIdx];
      assert a[j] <= a[k];
    }
  }

  // Prove cross property: forall p < i+1 <= k < n, a[p] <= a[k]
  assert forall p,k | 0 <= p < i+1 <= k < a.Length {
    if p < i {
      // p < i
      if k == minIdx {
        // k is the swapped position: a[k] == oldSeq[i]
        assert a[p] == oldSeq[p];
        assert a[k] == oldSeq[i];
        // oldSeq[p] <= oldSeq[minIdx] and oldSeq[minIdx] <= oldSeq[i] (minIdx minimal), so oldSeq[p] <= oldSeq[i]
        assert oldSeq[p] <= oldSeq[minIdx];
        assert oldSeq[minIdx] <= oldSeq[i];
        assert a[p] <= a[k];
      } else {
        // k is unchanged, a[k] == oldSeq[k]
        assert a[p] == oldSeq[p];
        assert a[k] == oldSeq[k];
        assert oldSeq[p] <= oldSeq[k];
        assert a[p] <= a[k];
      }
    } else {
      // p == i
      assert a[p] == oldSeq[minIdx];
      if k == minIdx {
        // k == minIdx, a[k] == oldSeq[i]
        assert a[k] == oldSeq[i];
        // oldSeq[minIdx] <= oldSeq[i]
        assert oldSeq[minIdx] <= oldSeq[i];
        assert a[p] <= a[k];
      } else {
        // k != minIdx, a[k] == oldSeq[k]
        assert a[k] == oldSeq[k];
        // oldSeq[minIdx] <= oldSeq[k]
        assert oldSeq[minIdx] <= oldSeq[k];
        assert a[p] <= a[k];
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
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted(a, 0, i)
    invariant forall p,k :: 0 <= p < i <= k < n ==> a[p] <= a[k]
  {
    var minIdx := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIdx < j
      invariant forall t :: i <= t < j ==> a[minIdx] <= a[t]
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    ghost var oldSeq := a[..];
    var tmp := a[i];
    a[i] := a[minIdx];
    a[minIdx] := tmp;
    SwapMaintains(oldSeq, a, i, minIdx);
    i := i + 1;
  }
}
// </vc-code>

