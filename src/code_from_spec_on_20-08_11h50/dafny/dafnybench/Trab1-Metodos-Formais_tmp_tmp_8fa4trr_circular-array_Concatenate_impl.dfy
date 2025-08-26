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
  method AsSequence() returns (s: seq<int>)
    ensures s == Elements
    {
      s := if start + size <= arr.Length
           then arr[start..start + size]
           else arr[start..] + arr[..size - (arr.Length - start)];
    }

  /*
    Concatenate method.
  */

// <vc-helpers>
  method EnqueueElement(e: int)
    requires !IsFull()
    modifies this`size, this`Elements, this.arr
    ensures size == old(size) + 1
    ensures Elements == old(Elements) + [e]
    ensures start == old(start)
    ensures Capacity == old(Capacity)
    ensures arr == old(arr)
  {
    var insertPos := (start + size) % arr.Length;
    arr[insertPos] := e;
    size := size + 1;
    
    // Update the ghost variable Elements to maintain the invariant
    if start + old(size) <= arr.Length then
      if start + size <= arr.Length then
        Elements := arr[start..start + size];
      else
        Elements := arr[start..] + arr[..size - (arr.Length - start)];
    else
      Elements := arr[start..] + arr[..size - (arr.Length - start)];
  }
// </vc-helpers>

method Concatenate(q1: CircularArray) returns(q2: CircularArray)
    requires q1.Valid()
    requires q1 != this
    ensures fresh(q2)
    ensures q2.Capacity == Capacity + q1.Capacity
    ensures q2.Elements == Elements + q1.Elements
// </vc-spec>
// <vc-code>
{
  var newCapacity := arr.Length + q1.arr.Length;
  q2 := new CircularArray.EmptyQueue(newCapacity);
  
  // Get sequences from both arrays
  var thisSeq := AsSequence();
  var q1Seq := q1.AsSequence();
  
  // Copy elements from this array
  var i := 0;
  while i < |thisSeq|
    invariant 0 <= i <= |thisSeq|
    invariant q2.size == i
    invariant q2.Capacity == newCapacity
    invariant q2.Elements == thisSeq[..i]
    invariant q2.size < q2.Capacity
    modifies q2`size, q2`Elements, q2.arr
  {
    q2.EnqueueElement(thisSeq[i]);
    i := i + 1;
  }
  
  // Copy elements from q1 array  
  var j := 0;
  while j < |q1Seq|
    invariant 0 <= j <= |q1Seq|
    invariant q2.size == |thisSeq| + j
    invariant q2.Capacity == newCapacity
    invariant q2.Elements == thisSeq + q1Seq[..j]
    invariant q2.size <= q2.Capacity
    modifies q2`size, q2`Elements, q2.arr
  {
    q2.EnqueueElement(q1Seq[j]);
    j := j + 1;
  }
}
// </vc-code>

}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/