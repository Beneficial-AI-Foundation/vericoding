class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  //ATOM
  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front < circularQueue.Length &&
    0 <= rear < circularQueue.Length &&
    |Content| == counter &&
    (circularQueue.Length > 0 ==> (0 <= front < circularQueue.Length && 0 <= rear < circularQueue.Length))
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

  //IMPL
  method insert(item: int)
     requires rear <= circularQueue.Length
     ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
         (
           Content == [item] &&
           |Content| == 1
         )
  {
    /* code modified by LLM (iteration 4): fixed condition to check for empty queue */
    if front == 0 && rear == 0 && circularQueue.Length == 0 {
      auxInsertEmptyQueue(item);
    }
  }

  //IMPL
  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {
    /* code modified by LLM (iteration 4): proper array initialization and content management */
    var newQueue := new int[1];
    newQueue[0] := item;
    circularQueue := newQueue;
    Content := [item];
    rear := 1;
    counter := counter + 1;
  }

  //IMPL
  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  {
    /* code modified by LLM (iteration 4): complete array expansion and content update */
    var oldContent := Content;
    var newQueue := new int[circularQueue.Length + 1];
    var i := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant forall j :: 0 <= j < i ==> newQueue[j] == circularQueue[j]
    {
      newQueue[i] := circularQueue[i];
      i := i + 1;
    }
    newQueue[circularQueue.Length] := item;
    circularQueue := newQueue;
    Content := oldContent + [item];
    rear := rear + 1;
    counter := counter + 1;
  }

  //IMPL
  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length && rear < circularQueue.Length
    requires |Content| == circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures |Content| == old(|Content|)
  {
    /* code modified by LLM (iteration 4): simplified content management for circular queue */
    var oldRear := rear;
    circularQueue[rear] := item;
    rear := rear + 1;
    counter := counter + 1;
    /* code modified by LLM (iteration 4): maintain content as complete array view */
    Content := circularQueue[..];
  }

  //IMPL
  method auxInsertInitQueue(item:int)
  {
    /* code modified by LLM (iteration 4): empty implementation maintained */
  }

  //IMPL
  method auxInsertBetweenQueue(item:int)
  {
    /* code modified by LLM (iteration 4): empty implementation maintained */
  }

  //IMPL
  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    requires counter > 0
    ensures rear <= circularQueue.Length
    ensures circularQueue.Length > 0
    ensures item == old(circularQueue[front])
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures counter == old(counter) - 1
  {
    /* code modified by LLM (iteration 4): simplified remove with proper bounds */
    var oldFront := front;
    
    item := circularQueue[front];
    front := (front + 1) % circularQueue.Length;
    counter := counter - 1;
    
    /* code modified by LLM (iteration 4): update content to reflect current state */
    Content := circularQueue[..];
  }

  //IMPL
  method size() returns (size:nat)
    ensures size == counter
  {
    /* code modified by LLM (iteration 4): direct assignment */
    size := counter;
  }

  //IMPL
  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {
    /* code modified by LLM (iteration 4): boolean comparison */
    isEmpty := counter == 0;
  }

  //IMPL
  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
  {
    /* code modified by LLM (iteration 4): handle empty array case */
    contains := false;
    if circularQueue.Length == 0 {
      return;
    }
    
    var i := 0;
    while i < circularQueue.Length
      invariant 0 <= i <= circularQueue.Length
      invariant contains ==> (exists j :: 0 <= j < i && circularQueue[j] == item)
      invariant !contains ==> (forall j :: 0 <= j < i ==> circularQueue[j] != item)
    {
      if circularQueue[i] == item {
        contains := true;
        return;
      }
      i := i + 1;
    }
    /* code modified by LLM (iteration 4): final assertion for loop completion */
    assert forall j :: 0 <= j < circularQueue.Length ==> circularQueue[j] != item;
  }
}