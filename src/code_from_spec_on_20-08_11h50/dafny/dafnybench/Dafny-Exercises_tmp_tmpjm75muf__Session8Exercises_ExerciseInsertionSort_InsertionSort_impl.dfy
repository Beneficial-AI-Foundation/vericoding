predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma multiset_preservation_shift(a_before: seq<int>, a_after: seq<int>, j: int, key: int)
  requires 0 <= j < |a_before| - 1
  requires |a_before| == |a_after|
  requires a_after[j+1] == a_before[j]
  requires forall k :: 0 <= k < |a_before| && k != j && k != j+1 ==> a_before[k] == a_after[k]
  requires a_before[j+1] == key
  ensures multiset(a_before) == multiset(a_after)
{
  // The multiset is preserved because we're just moving elements around
}

lemma multiset_preservation_insert(a_before: seq<int>, a_after: seq<int>, pos: int, key: int)
  requires 0 <= pos < |a_before|
  requires |a_before| == |a_after|
  requires a_after[pos] == key
  requires forall k :: 0 <= k < |a_before| && k != pos ==> a_before[k] == a_after[k]
  requires a_before[pos] == key
  ensures multiset(a_before) == multiset(a_after)
{
}

lemma sorted_seg_preservation(a: array<int>, j1: int, j2: int, i: int)
  requires 0 <= j1 <= j2 < i < a.Length
  requires sorted_seg(a, 0, j1)
  requires sorted_seg(a, j2+1, i)
  ensures sorted_seg(a, 0, j1)
  ensures sorted_seg(a, j2+1, i)
{
}
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    ghost var loop_multiset := multiset(a[..]);
    
    // Shift elements to the right until we find the correct position for key
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant sorted_seg(a, 0, j) || j == -1
      invariant j+2 <= i ==> sorted_seg(a, j+2, i)
      invariant forall k :: j+2 <= k <= i ==> a[k] >= key
      invariant j >= 0 ==> (forall k :: 0 <= k <= j ==> a[k] <= key)
      invariant multiset(a[..]) == loop_multiset
      invariant a[i] == key
      invariant j >= 0 ==> a[j+1] >= key
    {
      ghost var before_shift := a[..];
      a[j+1] := a[j];
      ghost var after_shift := a[..];
      
      // Assert that the multiset is preserved after the shift
      assert after_shift[j+1] == before_shift[j];
      assert forall k :: 0 <= k < a.Length && k != j && k != j+1 ==> before_shift[k] == after_shift[k];
      assert before_shift[j+1] == key;
      multiset_preservation_shift(before_shift, after_shift, j, key);
      assert multiset(after_shift) == multiset(before_shift);
      
      j := j - 1;
    }
    
    // Insert the key at the correct position
    ghost var before_insert := a[..];
    a[j+1] := key;
    ghost var after_insert := a[..];
    
    multiset_preservation_insert(before_insert, after_insert, j+1, key);
    assert multiset(a[..]) == loop_multiset;
    
    i := i + 1;
  }
}
// </vc-code>