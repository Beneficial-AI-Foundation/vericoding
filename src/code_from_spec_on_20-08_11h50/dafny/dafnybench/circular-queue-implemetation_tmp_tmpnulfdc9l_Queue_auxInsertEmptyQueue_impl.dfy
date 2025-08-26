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
// <vc-spec>
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

// <vc-helpers>
// </vc-helpers>

method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
// </vc-spec>
// <vc-code>
{
  var newArray := new int[1];
  newArray[0] := item;
  circularQueue := newArray;
  rear := 1;
  counter := counter + 1;
  Content := [item];
}
// </vc-code>

// TODO
}