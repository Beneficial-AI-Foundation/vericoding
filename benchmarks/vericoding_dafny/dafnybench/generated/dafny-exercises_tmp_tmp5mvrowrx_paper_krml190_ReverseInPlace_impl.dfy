// Examples used in paper:
//   Specification and Verification of Object-Oriented Software
// by K. Rustan M. Leino
// link of the paper:
//   http://leino.science/papers/krml190.pdf

// Figure 0. An example linked-list program written in Dafny.
class Data { }

class Node {
  var list: seq<Data>
  var footprint: set<Node>

  var data: Data
  var next: Node?

// <vc-spec>
  function Valid(): bool
    reads this, footprint
  {
    this in footprint &&
    (next == null ==> list  == [data]) &&
    (next != null ==> next in footprint &&
                      next.footprint <= footprint &&
                      !(this in next.footprint) &&
                      list == [data] + next.list &&
                      next.Valid())
  }

  constructor(d: Data)
    ensures Valid() && fresh(footprint - {this})
    ensures list == [d]
  {
    data := d;
    next := null;
    list := [d];
    footprint := {this};
  }



  // Figure 1: The Node.ReverseInPlace method,
  //     which performs an in situ list reversal.

// <vc-helpers>
  predicate ValidReversed(prev: Node?)
    reads this, footprint, if prev != null then {prev} + prev.footprint else {}
  {
    prev == null || (prev.Valid() && prev.footprint <= footprint && !(this in prev.footprint))
  }

  lemma ValidReversedLemma(prev: Node?, newFootprint: set<Node>)
    requires prev == null || prev.Valid()
    requires prev == null || prev.footprint <= newFootprint
    requires this !in (if prev != null then prev.footprint else {})
    requires this in newFootprint
    ensures prev == null || (prev.Valid() && prev.footprint <= newFootprint && !(this in prev.footprint))
  {
  }
// </vc-helpers>

method ReverseInPlace() returns (reverse: Node)
    requires Valid()
    modifies footprint
    ensures reverse.Valid()
    // isn't here a typo?
    ensures fresh(reverse.footprint - old(footprint))
    ensures |reverse.list| == |old(list)|
    ensures forall i | 0 <= i < |old(list)| :: old(list)[i] == reverse.list[|old(list)| - 1 - i]
// </vc-spec>
// <vc-code>
{
  var current: Node? := this;
  var prev: Node? := null;
  ghost var originalList := list;
  ghost var originalFootprint := footprint;
  ghost var processedNodes := 0;
  
  while current != null
    invariant current == null ==> prev != null && prev.Valid()
    invariant current != null ==> current in originalFootprint
    invariant prev == null || prev.Valid()
    invariant current != null ==> ValidReversed(prev)
    invariant prev == null || prev.footprint <= originalFootprint
    invariant current != null ==> (prev == null || !(current in prev.footprint))
    invariant processedNodes >= 0
    invariant current != null ==> processedNodes < |originalList|
    invariant current == null ==> processedNodes == |originalList|
    invariant prev != null ==> |prev.list| == processedNodes
    invariant current != null ==> current.Valid()
    invariant current != null ==> current.footprint <= originalFootprint
    decreases |originalList| - processedNodes
  {
    ghost var oldProcessedNodes := processedNodes;
    var oldNext := current.next;
    current.next := prev;
    
    // Update the list representation
    if prev == null {
      current.list := [current.data];
      current.footprint := {current};
    } else {
      current.list := [current.data] + prev.list;
      current.footprint := {current} + prev.footprint;
    }
    
    // Prove ValidReversed will hold
    if oldNext != null {
      ValidReversedLemma(current, originalFootprint);
    }
    
    prev := current;
    current := oldNext;
    processedNodes := processedNodes + 1;
    
    // Help prove invariants
    assert processedNodes == oldProcessedNodes + 1;
    assert prev != null && |prev.list| == processedNodes;
    if current == null {
      assert processedNodes == |originalList|;
    } else {
      assert processedNodes < |originalList|;
    }
  }
  
  reverse := prev;
  
  // Assert the postcondition to help verification
  assert reverse.Valid();
  assert |reverse.list| == |originalList|;
}
// </vc-code>

}