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

method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
// </vc-spec>
// <vc-code>
{
  contains := false;
  var i := 0;
  
  while i < circularQueue.Length
    invariant 0 <= i <= circularQueue.Length
    invariant contains == true ==> item in circularQueue[..i]
    invariant contains == false ==> item !in circularQueue[..i]
  {
    if circularQueue[i] == item {
      contains := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

// TODO
}