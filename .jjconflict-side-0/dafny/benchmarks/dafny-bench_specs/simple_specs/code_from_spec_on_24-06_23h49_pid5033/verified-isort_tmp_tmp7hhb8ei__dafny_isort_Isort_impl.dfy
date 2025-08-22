//ATOM
// Dafny is designed to be familiar to those programming in an OOP language like
// Java, so, we have plain old ordinary mutable arrays rather than the functional
// list data structures that we saw in Coq. This means that unlike our Coq
// and Python examples, we can sort our array in-place and avoid needing a whole
// bunch of intermediary allocations.

// Just as before, we need a way of defining what it means for an array of nats
// to be sorted:
predicate sorted(a: seq<nat>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

//IMPL
method Isort(a: array<nat>)
  modifies a
  ensures sorted(a[..])
{
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted(a[0..i])
  {
    var key := a[i];
    var j := i - 1;
    
    /* code modified by LLM (iteration 3): Store original array state to track permutation */
    ghost var old_a := a[0..i+1];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      /* code modified by LLM (iteration 3): Simplified invariants that correctly capture the shifting */
      invariant forall k :: j+2 <= k <= i ==> a[k] > key
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[k+1]
      invariant sorted(a[0..j+1])
      /* code modified by LLM (iteration 3): Ensure elements beyond the shifted region are preserved */
      invariant forall k :: i+1 <= k < a.Length ==> a[k] == old(a[k])
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    
    /* code modified by LLM (iteration 3): Add assertion to help prove the key insight */
    assert forall k :: 0 <= k <= j ==> a[k] <= key;
    assert forall k :: j+2 <= k <= i ==> a[k] >= key;
    assert sorted(a[0..i+1]);
    
    i := i + 1;
  }
}