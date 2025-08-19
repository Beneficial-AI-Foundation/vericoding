// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

// <vc-spec>
predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

// <vc-helpers>
// </vc-helpers>

method MainMethod(y: Node)
  modifies y
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>