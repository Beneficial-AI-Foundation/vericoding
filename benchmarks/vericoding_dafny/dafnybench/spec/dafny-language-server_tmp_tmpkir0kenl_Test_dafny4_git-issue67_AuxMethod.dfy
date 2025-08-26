// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

// <vc-helpers>
// </vc-helpers>

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
// <vc-code>
{
  assume false;
}
// </vc-code>