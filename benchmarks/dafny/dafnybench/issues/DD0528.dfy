// <vc-preamble>
class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    counter := 0;
  } //[tam] ; [1, 2, 3, 4]
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
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
      //counter := counter + 1;
      // if front == 0 && rear == 0 && circularQueue.Length == 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   queueInsert[0] := item;
      //   circularQueue := queueInsert;
      //   Content := [item];
      //   rear := rear + 1;
      // }   
      // else if front == 0 && rear == circularQueue.Length-1 && circularQueue.Length > 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   var i: nat := 0;
      //   while i < circularQueue.Length
      //   invariant circularQueue.Length + 1 == queueInsert.Length
      //   {
      //     queueInsert[i] := circularQueue[i];
      //     i := i + 1;
      //   }
      //   queueInsert[queueInsert.Length - 1] := item;
      //   Content := Content + [item];
      //   rear := rear + 1;
      //   circularQueue := queueInsert;
      // }
}
// </vc-code>

// TODO
}