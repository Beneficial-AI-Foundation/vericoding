// <vc-preamble>
/*
  Class CircularArray.

  Names:
  Arthur Sudbrack Ibarra,
  Miguel Torres de Castro,
  Felipe Grosze Nipper,
  Willian Magnum Albeche,
  Luiz Eduardo Mello dos Reis.
*/
class {:autocontracts} CircularArray {
  /*
    Implementation
  */
  var arr: array<int>; // The array.
  var start: nat; // The index of the first element.
  var size: nat; // The number of elements in the queue.

  /*
    Abstraction.
  */
  ghost const Capacity: nat; // The capacity of the queue. (WE WERE UNABLE TO MAKE THE SIZE OF THE ARRAY DYNAMIC).
  ghost var Elements: seq<int>; // The elements in the array represented as a sequence.

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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
// </vc-spec>
// <vc-code>
{
    e := arr[start];
    if start + 1 < arr.Length {
      start := start + 1;
    }
    else {
      start := 0;
    }
    size := size - 1;
    Elements := Elements[1..];
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