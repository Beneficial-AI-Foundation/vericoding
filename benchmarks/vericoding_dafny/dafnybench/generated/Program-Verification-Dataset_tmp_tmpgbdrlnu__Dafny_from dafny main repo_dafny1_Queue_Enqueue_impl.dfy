// RUN: %testDafnyForEachResolver "%s"


// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

class Queue<T(0)> {

// <vc-spec>
method Front() returns (x: int)
{
    x := 0; // Placeholder
}



  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var footprint: set<object>
  ghost var spine: set<Node<T>>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint && spine <= footprint &&
    head in spine &&
    tail in spine &&
    tail.next == null &&
    (forall n ::
      n in spine ==>
        n.footprint <= footprint && this !in n.footprint &&
        n.Valid() &&
        (n.next == null ==> n == tail)) &&
    (forall n ::
      n in spine ==>
        n.next != null ==> n.next in spine) &&
    contents == head.tailContents
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures |contents| == 0
  {
    var n: Node<T> := new Node<T>.Init();
    head := n;
    tail := n;
    contents := n.tailContents;
    footprint := {this} + n.footprint;
    spine := {n};
  }

// <vc-helpers>
// </vc-helpers>

method Enqueue(t: T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents) + [t]
// </vc-spec>
// <vc-code>
{
  var newNode := new Node<T>.Init();
  newNode.data := t;
  
  // Update the current tail to point to the new node
  tail.next := newNode;
  tail.tailContents := [newNode.data] + newNode.tailContents;
  tail.footprint := tail.footprint + newNode.footprint;
  
  // Update all nodes in the spine to include the new node in their footprint
  // and update their tailContents
  var current := head;
  ghost var visited: set<Node<T>> := {};
  while current != tail
    invariant current in spine
    invariant current.footprint <= footprint + newNode.footprint
    invariant visited <= spine
    invariant current !in visited
    decreases spine - visited
    modifies spine
  {
    current.tailContents := current.tailContents + [t];
    current.footprint := current.footprint + newNode.footprint;
    visited := visited + {current};
    current := current.next;
  }
  
  // Move the tail pointer to the new node
  tail := newNode;
  
  // Update queue's ghost state
  spine := spine + {newNode};
  footprint := {this} + footprint + newNode.footprint;
  contents := head.tailContents;
}
// </vc-code>

}

class Node<T(0)> {
  var data: T
  var next: Node?<T>

  ghost var tailContents: seq<T>
  ghost var footprint: set<object>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint &&
    (next != null ==> next in footprint && next.footprint <= footprint) &&
    (next == null ==> tailContents == []) &&
    (next != null ==> tailContents == [next.data] + next.tailContents)
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures next == null
  {
    next := null;
    tailContents := [];
    footprint := {this};
  }
}