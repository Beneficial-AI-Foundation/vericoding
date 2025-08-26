// Sorts array 'a' using the insertion sort algorithm.

// <vc-helpers>
// Helper lemmas for multiset properties
lemma MultisetSliceProperty<T>(s: seq<T>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    ensures multiset(s[i..k]) == multiset(s[i..j]) + multiset(s[j..k])
{
    if i == j {
        assert s[i..k] == s[j..k];
        assert s[i..j] == [];
    } else if j == k {
        assert s[i..k] == s[i..j];
        assert s[j..k] == [];
    } else {
        assert s[i..k] == s[i..j] + s[j..k];
    }
}

lemma MultisetUpdateProperty<T>(s: seq<T>, i: int, v: T)
    requires 0 <= i < |s|
    ensures multiset(s[i := v]) == multiset(s) - multiset([s[i]]) + multiset([v])
{
}

lemma MultisetShiftProperty(s: seq<int>, i: int, j: int)
    requires 0 <= j < i < |s|
    ensures multiset(s[i := s[j]]) == multiset(s) - multiset([s[i]]) + multiset([s[j]])
{
    MultisetUpdateProperty(s, i, s[j]);
}
// </vc-helpers>

// <vc-spec>
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  ghost var originalArray := a[..];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(originalArray)
  {
    var key := a[i];
    var j := i - 1;
    
    ghost var oldArray := a[..];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant isSorted(a, 0, j + 1)
      invariant isSorted(a, j + 2, i + 1)
      invariant forall k :: j + 2 <= k <= i ==> a[k] >= key
      invariant multiset(a[..]) == multiset(oldArray)
      invariant forall k :: j + 2 <= k <= i ==> a[k] == oldArray[k - 1]
      invariant j >= 0 ==> forall k :: 0 <= k <= j ==> a[k] <= key || a[k] == oldArray[k]
      decreases j
    {
      ghost var beforeShift := a[..];
      a[j + 1] := a[j];
      ghost var afterShift := a[..];
      
      // Prove multiset is preserved after the shift
      assert afterShift == beforeShift[j + 1 := beforeShift[j]];
      MultisetShiftProperty(beforeShift, j + 1, j);
      assert multiset(afterShift) == multiset(beforeShift);
      
      j := j - 1;
    }
    
    ghost var beforeInsert := a[..];
    a[j + 1] := key;
    ghost var afterInsert := a[..];
    
    // Prove multiset is preserved after inserting key
    assert afterInsert == beforeInsert[j + 1 := key];
    assert key == oldArray[i];
    MultisetUpdateProperty(beforeInsert, j + 1, key);
    assert multiset(afterInsert) == multiset(beforeInsert) - multiset([beforeInsert[j + 1]]) + multiset([key]);
    assert multiset(afterInsert) == multiset(oldArray);
    assert multiset(oldArray) == multiset(originalArray);
    
    i := i + 1;
  }
}
// </vc-code>

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Simple test case to check the postcondition