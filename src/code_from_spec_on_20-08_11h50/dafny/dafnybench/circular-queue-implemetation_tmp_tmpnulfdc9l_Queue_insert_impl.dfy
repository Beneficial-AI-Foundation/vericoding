class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>
  var rear: nat  // cauda
  var front: nat // head
  var counter: nat

  // Abstração
  ghost var Content: seq<int>

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front < circularQueue.Length &&
    0 <= rear < circularQueue.Length &&
    Content == if counter == 0 then [] 
               else if front <= rear then circularQueue[front..rear+1]
               else circularQueue[front..] + circularQueue[..rear+1]
  }

  // Construtor
// <vc-spec>
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
// </vc-spec>
// <vc-code>
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  } //[tam] ; [1, 2, 3, 4]
// </vc-code>

// <vc-helpers>
  ghost predicate ValidForNonEmpty()
    requires circularQueue.Length > 0
  {
    0 < counter <= circularQueue.Length &&
    0 <= front < circularQueue.Length &&
    0 <= rear < circularQueue.Length &&
    Content == if front <= rear then circularQueue[front..rear+1]
               else circularQueue[front..] + circularQueue[..rear+1]
  }

  ghost predicate Valid()
  {
    if circularQueue.Length == 0 then
      counter == 0 && Content == []
    else
      0 <= counter <= circularQueue.Length &&
      0 <= front < circularQueue.Length &&
      0 <= rear < circularQueue.Length &&
      Content == if counter == 0 then [] 
                 else if front <= rear then circularQueue[front..rear+1]
                 else circularQueue[front..] + circularQueue[..rear+1]
  }
// </vc-helpers>

method insert(item: int)
    // requires rear <= circularQueue.Length
    // ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == [item] &&
    //       |Content| == 1
    //     )
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
// </vc-spec>
// <vc-code>
{
  if circularQueue.Length == 0 {
    // Create new array with single element
    var newArray := new int[1];
    newArray[0] := item;
    circularQueue := newArray;
    rear := 0;
    front := 0;
    counter := 1;
    Content := [item];
  } else if counter == circularQueue.Length {
    // Array is full, need to resize
    var newArray := new int[circularQueue.Length * 2];
    var i := 0;
    var j := front;
    
    // Copy existing elements in order
    while i < counter
      invariant 0 <= i <= counter
      invariant i < newArray.Length
      invariant newArray.Length == circularQueue.Length * 2
      invariant j == (front + i) % circularQueue.Length
      invariant 0 <= j < circularQueue.Length
      invariant forall k :: 0 <= k < i ==> newArray[k] == circularQueue[(front + k) % circularQueue.Length]
    {
      newArray[i] := circularQueue[j];
      i := i + 1;
      j := (j + 1) % circularQueue.Length;
    }
    
    // Add new item
    newArray[counter] := item;
    circularQueue := newArray;
    front := 0;
    rear := counter;
    counter := counter + 1;
    Content := Content + [item];
  } else {
    // Array has space, just add the item
    rear := (rear + 1) % circularQueue.Length;
    circularQueue[rear] := item;
    counter := counter + 1;
    Content := Content + [item];
  }
}
// </vc-code>

// TODO
}