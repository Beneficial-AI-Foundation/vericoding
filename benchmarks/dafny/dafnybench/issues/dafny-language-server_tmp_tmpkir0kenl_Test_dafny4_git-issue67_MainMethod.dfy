// <vc-preamble>
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MainMethod(y: Node)
  modifies y
// </vc-spec>
// <vc-code>
{
  AuxMethod(y);  // remove this call and the assertion below goes through (as it should)

  forall x | Q(x)
    ensures P(x)
  {
    assume false;
  }
  // The following assertion should be a direct consequence of the forall statement above
  assert forall x :: Q(x) ==> P(x);
}
// </vc-code>
