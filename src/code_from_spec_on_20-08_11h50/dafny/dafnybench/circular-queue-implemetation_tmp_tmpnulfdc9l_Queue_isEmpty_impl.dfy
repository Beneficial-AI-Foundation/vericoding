// The specification requires:
// - If `isEmpty` returns `true`, then `counter == 0`
// - If `isEmpty` returns `false`, then `counter != 0`
//
// This is a straightforward implementation that just needs to check if the counter is zero.

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

method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
// </vc-spec>
// <vc-code>
{
  isEmpty := counter == 0;
}
// </vc-code>

// TODO
}