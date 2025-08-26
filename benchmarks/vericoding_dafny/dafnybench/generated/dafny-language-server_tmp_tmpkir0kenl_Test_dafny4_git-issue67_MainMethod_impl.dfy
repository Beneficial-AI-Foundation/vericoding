class Node { }

predicate Q(x: Node)
predicate P(x: Node)

// <vc-spec>
method AuxMethod(y: Node)
  modifies y

// <vc-helpers>
// </vc-helpers>

method MainMethod(y: Node)
  modifies y
// </vc-spec>
// <vc-code>
{
}
// </vc-code>