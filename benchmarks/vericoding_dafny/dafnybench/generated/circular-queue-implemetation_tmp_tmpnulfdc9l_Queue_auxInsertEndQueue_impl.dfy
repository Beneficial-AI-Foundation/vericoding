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
    |Content| == counter &&
    (counter == 0 ==> Content == []) &&
    (counter > 0 && front <= rear ==> Content == circularQueue[front..rear+1]) &&
    (counter > 0 && front > rear ==> Content == circularQueue[front..] + circularQueue[0..rear+1])
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

method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
// </vc-spec>
// <vc-code>
{
  // Store old values for reference
  ghost var oldContent := Content;
  ghost var oldRear := rear;
  ghost var oldCounter := counter;
  
  counter := counter + 1;
  var queueInsert: array<int>;
  queueInsert := new int [circularQueue.Length + 1];
  var i: nat := 0;
  
  while i < circularQueue.Length
  invariant circularQueue.Length + 1 == queueInsert.Length
  invariant 0 <= i <= circularQueue.Length
  invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
  invariant Content == oldContent
  {
    queueInsert[i] := circularQueue[i];
    i := i + 1;
  }
  queueInsert[queueInsert.Length - 1] := item;
  
  // Update the circular queue and rear pointer
  circularQueue := queueInsert;
  rear := rear + 1;
  front := 0;
  
  // Update Content to reflect the new queue state
  Content := oldContent + [item];
  
  // Prove postconditions
  assert rear == oldRear + 1;
  assert counter == oldCounter + 1;
  assert Content == oldContent + [item];
  assert |Content| == |oldContent| + 1;
  assert front == 0;
}
// </vc-code>

// {
  //   counter := counter + 1;
  //   var queueInsert: array<int>;
  //   queueInsert := new int [circularQueue.Length + 1];
  //   var i: nat := 0;
  //   while i < circularQueue.Length
  //   invariant circularQueue.Length + 1 == queueInsert.Length
  //   invariant 0 <= i <= circularQueue.Length
  //   invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
  //   {
  //     queueInsert[i] := circularQueue[i];
  //     i := i + 1;
  //   }
  //   queueInsert[queueInsert.Length - 1] := item;
  //   Content := Content + [item];
  //   rear := rear + 1;
  //   circularQueue := queueInsert;
  // }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1

  method auxInsertInitQueue(item:int)

  method auxInsertBetweenQueue(item:int)

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  /*{
    if counter == 0 {
      item := -1;

    } else {
      item := circularQueue[front];
      front := (front + 1) % circularQueue.Length;
      counter := counter - 1;
    }
  }*/




  // TODO
}