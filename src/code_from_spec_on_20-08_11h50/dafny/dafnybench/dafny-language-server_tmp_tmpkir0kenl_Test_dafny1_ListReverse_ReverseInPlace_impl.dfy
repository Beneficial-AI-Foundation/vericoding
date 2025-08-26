// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var nxt: Node?

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r;
    requires (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    modifies r;
    ensures reverse == null || reverse in r;
    ensures (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    decreases *;
// </vc-spec>
// <vc-code>
{
  var current := x;
  var prev: Node? := null;
  
  while current != null
    invariant current == null || current in r;
    invariant prev == null || prev in r;
    invariant (forall y :: y in r ==> y.nxt == null || y.nxt in r);
    decreases *;
  {
    var next := current.nxt;
    current.nxt := prev;
    prev := current;
    current := next;
  }
  
  reverse := prev;
}
// </vc-code>

}