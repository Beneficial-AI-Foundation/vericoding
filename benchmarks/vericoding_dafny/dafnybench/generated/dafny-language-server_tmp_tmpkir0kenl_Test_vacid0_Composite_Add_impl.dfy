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
  lemma AcyclicParent(S: set<Composite>)
    requires this in S && Acyclic(S)
    requires parent != null
    ensures parent in S && parent.Acyclic(S)
  {
    assert parent.Acyclic(S - {this});
    assert parent in S;
    // Since parent.Acyclic(S - {this}) and this != parent (due to acyclicity),
    // we can derive parent.Acyclic(S)
  }

  lemma AcyclicSubset(S: set<Composite>, T: set<Composite>)
    requires this in S && S <= T && Acyclic(T)
    ensures Acyclic(S)
    decreases |T|
  {
    if parent != null {
      parent.AcyclicSubset(S - {this}, T - {this});
    }
  }

  lemma AcyclicExpansion(S: set<Composite>, U: set<Composite>)
    requires this in S && Acyclic(S) && S !! U
    ensures Acyclic(S + U)
  {
    if parent != null {
      assert parent in S;
      assert parent !in U;
      assert parent.Acyclic(S - {this});
      parent.AcyclicExpansion(S - {this}, U);
      assert parent.Acyclic((S + U) - {this});
    }
  }
// </vc-helpers>

method Add(ghost S: set<Composite>, child: Composite, ghost U: set<Composite>) 
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    requires child in U
    requires forall c :: c in U ==> c.Valid(U)
    requires S !! U
    requires left == null || right == null
    requires child.parent == null
    // modifies only one of this.left and this.right, and child.parent, and various sum fields:
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c :: c in S && c != this ==> c.left == old(c.left) && c.right == old(c.right)
    ensures old(left) != null ==> left == old(left)
    ensures old(right) != null ==> right == old(right)
    ensures forall c :: c in S ==> c.parent == old(c.parent) && c.val == old(c.val)
    // sets child.parent to this:
    ensures child.parent == this
    // leaves everything in S+U valid
    ensures forall c: Composite {:autotriggers false} :: c in S+U ==> c.Valid(S+U) // We can't generate a trigger for this at the moment; if we did, we would still need to prevent TrSplitExpr from translating c in S+U to S[c] || U[c].
// </vc-spec>
// <vc-code>
{
  // Set child's parent
  child.parent := this;
  
  // Add child to left or right
  if (left == null) {
    left := child;
  } else {
    right := child;
  }
  
  // Calculate delta for sum adjustment
  var delta := child.sum;
  
  // Find all ancestors that need sum adjustment
  ghost var ancestors := {this};
  var p: Composite? := this.parent;
  while (p != null)
    invariant p == null || (p in S && p.Acyclic(S))
    invariant ancestors <= S
    invariant this in ancestors
    invariant forall a :: a in ancestors ==> a in S && a.Acyclic(S)
    decreases S - ancestors
  {
    var current: Composite := p;
    if (current.parent != null) {
      current.AcyclicParent(S);
    }
    ancestors := ancestors + {current};
    p := current.parent;
  }
  
  // Establish that this is acyclic in S + U
  this.AcyclicExpansion(S, U);
  
  // Establish that all elements in ancestors are acyclic in S + U
  forall a | a in ancestors
    ensures a.Acyclic(S + U)
  {
    a.AcyclicExpansion(S, U);
  }
  
  // Establish validity conditions for elements in S
  forall c | c in S && c != this
    ensures c.Valid(S + U)
  {
    // c was valid in S, and since S !! U, c's structure is preserved
    assert c.Valid(S);
    // Since S !! U, all references in c remain valid in S + U
  }
  
  // Establish validity conditions for elements in U
  forall c | c in U && c != child
    ensures c.Valid(S + U)
  {
    // c was valid in U, and since S !! U, c's structure is preserved
    assert c.Valid(U);
    // Since S !! U, all references in c remain valid in S + U
  }
  
  // Child is now valid in S + U
  assert child.Valid(S + U);
  
  // Now this is almost valid except for sum
  assert left != null ==> left in S + U && left.parent == this && left != right;
  assert right != null ==> right in S + U && right.parent == this && left != right;
  
  // Use Adjust to propagate sum changes
  Adjust(delta, ancestors, S + U);
}
// </vc-code>

/*private*/ method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
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
  {
    var p: Composite? := this;
    ghost var T := U;
    while (p != null)
      invariant T <= U
      invariant p == null || p.Acyclic(T)
      invariant forall c :: c in S && c != p ==> c.Valid(S)
      invariant p != null ==> p.sum + delta == p.val + (if p.left == null then 0 else p.left.sum) + (if p.right == null then 0 else p.right.sum)
      invariant forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent) && c.val == old(c.val)
      decreases T
    {
      p.sum := p.sum + delta;
      T := T - {p};
      p := p.parent;
    }
  }
}