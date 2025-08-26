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
    (circularQueue.Length == 0 ==> front == 0 && rear == 0) &&
    (circularQueue.Length > 0 ==> 0 <= front < circularQueue.Length && 0 <= rear < circularQueue.Length) &&
    |Content| == counter &&
    (counter == 0 ==> Content == []) &&
    (counter > 0 ==> 
      (front <= rear ==> Content == circularQueue[front..rear+1]) &&
      (front > rear ==> Content == circularQueue[front..] + circularQueue[..rear+1])
    )
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



// remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção

// <vc-helpers>
// </vc-helpers>

method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    requires counter > 0
    requires |Content| > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[0]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[1..rear-old(front)+1]
    ensures old(front) >= rear ==> Content == old(Content)[1..]
// </vc-spec>
// <vc-code>
{
  item := circularQueue[front];
  var old_front := front;
  var old_content := Content;
  front := (front + 1) % circularQueue.Length;
  counter := counter - 1;
  
  if counter == 0 {
    Content := [];
  } else if old_front <= rear {
    // Update Content based on the Valid() predicate logic
    if front <= rear {
      Content := circularQueue[front..rear+1];
    } else {
      Content := circularQueue[front..] + circularQueue[..rear+1];
    }
  } else {
    // old_front > rear case
    if front <= rear {
      Content := circularQueue[front..rear+1];
    } else {
      Content := circularQueue[front..] + circularQueue[..rear+1];
    }
  }
}
// </vc-code>

// TODO
}