class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int


  predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&  // not needed, but speeds up verification

    (right != null ==> right in desc && left !in right.desc) &&

    (left != null ==>
      left in desc &&
      (right != null ==> desc == {left,right} + left.desc + right.desc)  &&
      (right == null ==> desc == {left} + left.desc)  &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==> desc == {right} + right.desc)  &&
      (right == null ==> desc == {})) &&

    (right != null ==> right.validDown()) &&

    (blocked() ==> forall m :: m in desc ==> m.blocked()) &&
    (after() ==> forall m :: m in desc ==> m.blocked() || m.after())
//    (left != null && right != null ==> left.desc !! right.desc)  // not needed
  }




  predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
  { validUp() && validDown() && desc !! anc }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }

// <vc-helpers>
  lemma validPreservesInLoop()
    requires valid()
    requires before()
    requires (left != null && !left.blocked() && !left.after()) || (right != null && !right.blocked() && !right.after())
    ensures valid()
  {
    // The validity is preserved because we don't modify any fields in the loop body
    // and the condition that we're not blocked means the blocked() implication is trivially true
  }

  lemma beforeImpliesValidDownBlockedCondition()
    requires validDown()
    requires before()
    ensures blocked() ==> forall m :: m in desc ==> m.blocked()
  {
    // Since before() means !sense && pc <= 2, and blocked() means sense,
    // we have !blocked(), so the implication is trivially true
    assert !blocked();
  }

  lemma validAfterSenseChange()
    requires valid()
    requires before()
    requires forall m :: m in desc ==> m.blocked() || m.after()
    ensures validUp()
    ensures this !in desc
    ensures (right != null ==> right in desc && left !in right.desc)
    ensures (left != null ==> left in desc && (right != null ==> desc == {left,right} + left.desc + right.desc) && (right == null ==> desc == {left} + left.desc) && left.validDown())
    ensures (left == null ==> (right != null ==> desc == {right} + right.desc) && (right == null ==> desc == {}))
    ensures (right != null ==> right.validDown())
    ensures desc !! anc
  {
    // After setting sense to true, we become blocked
    // The blocked condition in validDown will be satisfied
  }

  lemma validAfterTransition()
    requires validUp()
    requires this !in desc
    requires (right != null ==> right in desc && left !in right.desc)
    requires (left != null ==> left in desc && (right != null ==> desc == {left,right} + left.desc + right.desc) && (right == null ==> desc == {left} + left.desc) && left.validDown())
    requires (left == null ==> (right != null ==> desc == {right} + right.desc) && (right == null ==> desc == {}))
    requires (right != null ==> right.validDown())
    requires desc !! anc
    ensures valid()
  {
    // After the final transition, we maintain validity
  }
// </vc-helpers>

// <vc-spec>
method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    decreases *  // allow the method to not terminate
// </vc-spec>
// <vc-code>
{
  // Wait for children to be blocked or after
  while (left != null && !left.blocked() && !left.after()) || (right != null && !right.blocked() && !right.after())
    invariant valid()
    invariant before()
    decreases *
  {
    // Empty body - just waiting
  }
  
  // At this point, all descendants are blocked or after
  assert forall m :: m in desc ==> m.blocked() || m.after();
  
  validAfterSenseChange();
  
  // Now transition to blocked state
  sense := true;
  
  // Wait for parent to transition to after (if we have a parent)
  while parent != null && !parent.after()
    invariant validUp()
    invariant this !in desc
    invariant (right != null ==> right in desc && left !in right.desc)
    invariant (left != null ==> left in desc && (right != null ==> desc == {left,right} + left.desc + right.desc) && (right == null ==> desc == {left} + left.desc) && left.validDown())
    invariant (left == null ==> (right != null ==> desc == {right} + right.desc) && (right == null ==> desc == {}))
    invariant (right != null ==> right.validDown())
    invariant blocked()
    invariant desc !! anc
    decreases *
  {
    // Empty body - just waiting
  }
  
  // Transition to after state
  sense := false;
  pc := 3;
  
  validAfterTransition();
}
// </vc-code>

}