// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Composite {
  var left: Composite?
  var right: Composite?
  var parent: Composite?
  var val: int
  var sum: int

// <vc-spec>
  function Valid(S: set<Composite>): bool
    reads this, parent, left, right
  {
    this in S &&
    (parent != null ==> parent in S && (parent.left == this || parent.right == this)) &&
    (left != null ==> left in S && left.parent == this && left != right) &&
    (right != null ==> right in S && right.parent == this && left != right) &&
    sum == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
  }

  function Acyclic(S: set<Composite>): bool
    reads S
  {
    this in S &&
    (parent != null ==> parent.Acyclic(S - {this}))
  }

// <vc-helpers>
  lemma AcyclicSubset(U: set<Composite>)
    requires Acyclic(U)
    requires this in U
    ensures parent != null && parent in U ==> parent.Acyclic(U - {this})
  {
    if parent != null && parent in U {
      assert parent.Acyclic(U - {this});
    }
  }
// </vc-helpers>

method Adjust(delta: int, U: set<Composite>, S: set<Composite>)
    requires U <= S && Acyclic(U)
    // everything else is valid:
    requires forall c :: c in S && c != this ==> c.Valid(S)
    // this is almost valid:
    requires parent != null ==> parent in S && (parent.left == this || parent.right == this)
    requires left != null ==> left in S && left.parent == this && left != right
    requires right != null ==> right in S && right.parent == this && left != right
    // ... except that sum needs to be adjusted by delta:
    requires sum + delta == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
    // modifies sum fields in U:
    modifies U`sum
    // everything is valid, including this:
    ensures forall c :: c in S ==> c.Valid(S)
// </vc-spec>
// <vc-code>
{
  sum := sum + delta;
  if parent != null && parent in U {
    AcyclicSubset(U);
    parent.Adjust(delta, U - {this}, S);
  }
}
// </vc-code>

}