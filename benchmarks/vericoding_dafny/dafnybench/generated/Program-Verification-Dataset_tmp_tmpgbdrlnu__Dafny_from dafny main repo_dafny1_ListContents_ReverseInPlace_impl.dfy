class Node<T> {
  ghost var List: seq<T>
  ghost var Repr: set<Node<T>>

  var data: T
  var next: Node?<T>

  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (next == null ==> List == [data]) &&
    (next != null ==>
        next in Repr && next.Repr <= Repr &&
        this !in next.Repr &&
        List == [data] + next.List &&
        next.Valid())
  }

// <vc-spec>
  constructor (d: T)
    ensures Valid() && fresh(Repr)
    ensures List == [d]
  {
    data, next := d, null;
    List, Repr := [d], {this};
  }

  constructor InitAsPredecessor(d: T, succ: Node<T>)
    requires succ.Valid()
    ensures Valid() && fresh(Repr - succ.Repr)
    ensures List == [d] + succ.List
  {
    data, next := d, succ;
    List := [d] + succ.List;
    Repr := {this} + succ.Repr;
  }

// <vc-helpers>
  ghost function CollectData(nodes: seq<Node<T>>): seq<T>
    requires forall i :: 0 <= i < |nodes| ==> nodes[i] != null
    reads set i | 0 <= i < |nodes| :: nodes[i]
  {
    if |nodes| == 0 then []
    else [nodes[0].data] + CollectData(nodes[1..])
  }
  
  lemma ListReverseProperty(originalList: seq<T>, prevList: seq<T>, currentData: T, currentTail: seq<T>)
    requires |prevList| + 1 + |currentTail| == |originalList|
    requires forall i :: 0 <= i < |prevList| ==> prevList[i] == originalList[|originalList|-|currentTail|-1-1-i]
    requires currentData == originalList[|originalList|-|currentTail|-1]
    requires forall i :: 0 <= i < |currentTail| ==> currentTail[i] == originalList[|originalList|-|currentTail|+i]
    ensures forall i :: 0 <= i < |[currentData] + prevList| ==> ([currentData] + prevList)[i] == originalList[|originalList|-|currentTail|-1-i]
  {
    var newPrevList := [currentData] + prevList;
    forall i | 0 <= i < |newPrevList|
      ensures newPrevList[i] == originalList[|originalList|-|currentTail|-1-i]
    {
      if i == 0 {
        assert newPrevList[0] == currentData;
        assert currentData == originalList[|originalList|-|currentTail|-1];
        assert originalList[|originalList|-|currentTail|-1] == originalList[|originalList|-|currentTail|-1-0];
      } else {
        assert newPrevList[i] == prevList[i-1];
        assert prevList[i-1] == originalList[|originalList|-|currentTail|-1-1-(i-1)];
        assert originalList[|originalList|-|currentTail|-1-1-(i-1)] == originalList[|originalList|-|currentTail|-1-i];
      }
    }
  }
// </vc-helpers>

method ReverseInPlace() returns (reverse: Node<T>)
    requires Valid()
    modifies Repr
    ensures reverse.Valid() && reverse.Repr <= old(Repr)
    ensures |reverse.List| == |old(List)|
    ensures forall i :: 0 <= i < |reverse.List| ==> reverse.List[i] == old(List)[|old(List)|-1-i]
// </vc-spec>
// <vc-code>
{
  var current: Node?<T> := this;
  var prev: Node?<T> := null;
  ghost var originalList := List;
  
  while current != null
    decreases if current != null then |current.List| else 0
    invariant current == null ==> prev != null && prev.Valid()
    invariant current != null ==> current.Valid()
    invariant current == null ==> prev.Repr <= old(Repr)
    invariant current != null ==> current.Repr + (if prev != null then prev.Repr else {}) <= old(Repr)
    invariant prev == null ==> current != null
    invariant current == null ==> |prev.List| == |originalList|
    invariant prev != null && current != null ==> |prev.List| + |current.List| == |originalList|
    invariant current == null ==> (forall i :: 0 <= i < |prev.List| ==> prev.List[i] == originalList[|originalList|-1-i])
    invariant prev != null && current != null ==> prev.Repr !! current.Repr
    invariant prev != null && current != null ==> (forall i :: 0 <= i < |prev.List| ==> prev.List[i] == originalList[|originalList|-|current.List|-1-i])
    invariant originalList == old(List)
  {
    var nextNode := current.next;
    ghost var currentData := current.data;
    ghost var currentTail := if current.next != null then current.next.List else [];
    
    // Prove precondition for lemma when prev != null
    if prev != null {
      // Establish preconditions for ListReverseProperty
      assert |prev.List| + |current.List| == |originalList|;
      assert |prev.List| + 1 + |currentTail| == |originalList| by {
        if current.next != null {
          assert current.List == [current.data] + current.next.List;
          assert |current.List| == 1 + |current.next.List|;
          assert |currentTail| == |current.next.List|;
        } else {
          assert current.List == [current.data];
          assert |current.List| == 1;
          assert |currentTail| == 0;
        }
      }
      
      assert currentData == originalList[|originalList|-|currentTail|-1] by {
        assert currentData == current.data;
        assert current.List[0] == current.data;
        if current.next != null {
          assert |currentTail| == |current.next.List|;
          assert |current.List| == 1 + |currentTail|;
        } else {
          assert |currentTail| == 0;
          assert |current.List| == 1;
        }
        assert |prev.List| + |current.List| == |originalList|;
        // The current data should be at position |prev.List| in original list
        // But we need to account for the reversal pattern
      }
      
      ListReverseProperty(originalList, prev.List, currentData, currentTail);
    }
    
    // Modify the structure
    current.next := prev;
    
    // Update ghost variables to maintain validity
    if prev == null {
      current.List := [current.data];
      current.Repr := {current};
    } else {
      current.List := [current.data] + prev.List;
      current.Repr := {current} + prev.Repr;
    }
    
    prev := current;
    current := nextNode;
  }
  
  reverse := prev;
}
// </vc-code>

}