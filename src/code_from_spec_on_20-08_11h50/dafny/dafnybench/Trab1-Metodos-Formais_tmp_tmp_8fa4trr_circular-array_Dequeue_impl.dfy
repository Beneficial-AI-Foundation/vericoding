class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var arr: array<int> // The array.
  var start: nat // The index of the first element.
  var size: nat // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost const Capacity: nat // The capacity of the queue. (WE WERE UNABLE TO MAKE THE SIZE OF THE ARRAY DYNAMIC).
  ghost var Elements: seq<int> // The elements in the array represented as a sequence.

  /*
    Class invariant.
  */
  ghost predicate Valid()
  {
    0 <= start < arr.Length &&
    0 <= size <= arr.Length &&
    Capacity == arr.Length &&
    Elements == if start + size <= arr.Length
                then arr[start..start + size]
                else arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Constructor.
  */
// <vc-spec>
  constructor EmptyQueue(capacity: nat)
    requires capacity > 0
    ensures Elements == []
    ensures Capacity == capacity
  {
    arr := new int[capacity];
    start := 0;
    size := 0;
    Capacity := capacity;
    Elements := [];
  }

  /*
    Enqueue Method
  */

  /*
    Dequeue method.
  */

// <vc-helpers>
  lemma DequeueElementsLemma(oldStart: nat, oldSize: nat, newStart: nat, newSize: nat)
    requires 0 <= oldStart < arr.Length
    requires 0 <= oldSize <= arr.Length
    requires oldSize > 0
    requires newStart == (oldStart + 1) % arr.Length
    requires newSize == oldSize - 1
    requires 0 <= newStart < arr.Length
    requires 0 <= newSize <= arr.Length
    ensures var oldElements := if oldStart + oldSize <= arr.Length;
                              then arr[oldStart..oldStart + oldSize]
                              else arr[oldStart..] + arr[..oldSize - (arr.Length - oldStart)];
            var newElements := if newStart + newSize <= arr.Length;
                              then arr[newStart..newStart + newSize]
                              else arr[newStart..] + arr[..newSize - (arr.Length - newStart)];
            newElements == oldElements[1..]
  {
    var oldElements := if oldStart + oldSize <= arr.Length;
                      then arr[oldStart..oldStart + oldSize]
                      else arr[oldStart..] + arr[..oldSize - (arr.Length - oldStart)];
    var newElements := if newStart + newSize <= arr.Length;
                      then arr[newStart..newStart + newSize]
                      else arr[newStart..] + arr[..newSize - (arr.Length - newStart)];
    
    if oldStart + oldSize <= arr.Length {
      // Non-wrapping case
      if newStart + newSize <= arr.Length {
        // Still non-wrapping
        assert newElements == arr[newStart..newStart + newSize];
        assert oldElements == arr[oldStart..oldStart + oldSize];
        assert newStart == oldStart + 1;
        assert newSize == oldSize - 1;
        assert arr[newStart..newStart + newSize] == arr[oldStart + 1..oldStart + oldSize];
        assert arr[oldStart + 1..oldStart + oldSize] == arr[oldStart..oldStart + oldSize][1..];
      } else {
        // Now wrapping
        assert newStart == oldStart + 1;
        assert newSize == oldSize - 1;
        assert newStart + newSize > arr.Length;
        var wrapAmount := newSize - (arr.Length - newStart);
        assert newElements == arr[newStart..] + arr[..wrapAmount];
        assert oldElements == arr[oldStart..oldStart + oldSize];
        assert oldElements[1..] == arr[oldStart + 1..oldStart + oldSize];
        // The proof follows from sequence properties
      }
    } else {
      // Wrapping case
      assert oldElements == arr[oldStart..] + arr[..oldSize - (arr.Length - oldStart)];
      if newStart + newSize <= arr.Length {
        // Now non-wrapping
        assert newElements == arr[newStart..newStart + newSize];
        // Since we're unwrapping, newStart must be 0
        assert newStart == 0;
        assert oldStart == arr.Length - 1;
        assert newSize == oldSize - 1;
      } else {
        // Still wrapping
        assert newElements == arr[newStart..] + arr[..newSize - (arr.Length - newStart)];
        var oldWrapAmount := oldSize - (arr.Length - oldStart);
        var newWrapAmount := newSize - (arr.Length - newStart);
        
        if newStart == 0 {
          // Wrapped around
          assert oldStart == arr.Length - 1;
          assert newWrapAmount == oldWrapAmount - 1;
          assert newElements == arr[0..newWrapAmount];
          assert oldElements == arr[arr.Length - 1..] + arr[..oldWrapAmount];
          assert oldElements[1..] == arr[..oldWrapAmount];
          assert arr[..oldWrapAmount][..newWrapAmount] == arr[..newWrapAmount];
        } else {
          // Still in the wrapped portion
          assert newStart == oldStart + 1;
          assert newWrapAmount == oldWrapAmount;
          assert newElements == arr[newStart..] + arr[..newWrapAmount];
          assert oldElements == arr[oldStart..] + arr[..oldWrapAmount];
        }
      }
    }
  }
// </vc-helpers>

method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
// </vc-spec>
// <vc-code>
{
  // Store the old values for proof
  ghost var oldStart := start;
  ghost var oldSize := size;
  ghost var oldElements := Elements;
  
  // Get the first element
  e := arr[start];
  
  // Prove that e is the first element
  assert e == oldElements[0];
  
  // Update start and size
  start := (start + 1) % arr.Length;
  size := size - 1;
  
  // Update Elements based on the new configuration
  if start + size <= arr.Length {
    Elements := arr[start..start + size];
  } else {
    Elements := arr[start..] + arr[..size - (arr.Length - start)];
  }
  
  // Apply the lemma to prove the postcondition
  DequeueElementsLemma(oldStart, oldSize, start, size);
  
  // The postcondition should now follow
  assert Elements == oldElements[1..];
}
// </vc-code>

/*
    Contains predicate.
  */
  predicate Contains(e: int)
    ensures Contains(e) == (e in Elements)
  {
    if start + size < arr.Length then
      e in arr[start..start + size]
    else
      e in arr[start..] + arr[..size - (arr.Length - start)]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == |Elements|
  {
    size
  }

  /*
    IsEmpty predicate.
  */
  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    size == 0
  }

  /*
    IsFull predicate.
  */
  predicate IsFull()
    ensures IsFull() <==> |Elements| == Capacity
  {
    size == arr.Length
  }

  /*
    GetAt method.
    (Not requested in the assignment, but useful).
  */

  /*
    AsSequence method.
    (Auxiliary method for the Concatenate method)
  */

  /*
    Concatenate method.
  */
}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/