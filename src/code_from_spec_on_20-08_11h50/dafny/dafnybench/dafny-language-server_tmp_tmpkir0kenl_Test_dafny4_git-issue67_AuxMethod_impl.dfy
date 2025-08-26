// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
// </vc-spec>
// <vc-code>
{
  AuxMethod(y);
}
// </vc-code>