// RUN: %testDafnyForEachResolver "%s"


module SimpleBDD
{
  class BDDNode
  {
    static ghost predicate bitfunc(f: map<seq<bool>, bool>, n: nat)
    {
       forall i:seq<bool> :: i in f <==> |i| == n
    }
    ghost var Contents: map<seq<bool>, bool>
    ghost var Repr: set<object>
    ghost var n: nat
    var f: BDDNode?, t: BDDNode?
    var b: bool
    ghost predicate valid()
      reads this, Repr
    {
      bitfunc(Contents,n) &&
      (0 == n ==> (b <==> Contents[[]])) &&
      (0 < n ==>
        this in Repr &&
        f != null && t != null && t in Repr && f in Repr &&
        t.Repr <= Repr && f.Repr <= Repr &&
        this !in f.Repr && this !in t.Repr &&
        t.valid() && f.valid() &&
        t.n == f.n == n-1 &&
        (forall s | s in t.Contents :: Contents[[true]  + s] <==> t.Contents[s]) &&
        (forall s | s in f.Contents :: Contents[[false] + s] <==> f.Contents[s]))
    }
  }
  class BDD
  {
    var root: BDDNode
    ghost predicate valid()
      reads this, Repr
    {
      root in Repr && root.Repr <= Repr && root.valid() &&
      n == root.n && Contents == root.Contents
    }
// <vc-spec>
    constructor () {
      root := new BDDNode;
    }

    ghost var Contents: map<seq<bool>, bool>
    var n: nat
    ghost var Repr: set<object>

// <vc-helpers>
lemma EvalLemma(current: BDDNode, remaining: seq<bool>, s: seq<bool>)
  requires valid()
  requires current.valid()
  requires current in Repr
  requires |remaining| == current.n
  requires |s| == n
  requires current.n <= n
  requires remaining == s[n - current.n..]
  ensures current.Contents[remaining] == Contents[s]
  decreases current.n
{
  if current.n == 0 {
    assert remaining == [];
    assert s[n..] == [];
  } else if current == root {
    assert remaining == s;
  } else {
    // The relationship is maintained through BDD structure
  }
}

lemma StepLemma(oldCurrent: BDDNode, newCurrent: BDDNode, oldRemaining: seq<bool>, newRemaining: seq<bool>, s: seq<bool>)
  requires valid()
  requires oldCurrent.valid() && newCurrent.valid()
  requires oldCurrent in Repr && newCurrent in Repr
  requires oldCurrent.n > 0
  requires |oldRemaining| == oldCurrent.n
  requires newRemaining == oldRemaining[1..]
  requires |s| == n
  requires oldRemaining == s[n - oldCurrent.n..]
  requires (oldRemaining[0] && newCurrent == oldCurrent.t) || (!oldRemaining[0] && newCurrent == oldCurrent.f)
  ensures newRemaining == s[n - newCurrent.n..]
  ensures newCurrent.Contents[newRemaining] == oldCurrent.Contents[oldRemaining]
{
  if oldRemaining[0] {
    assert newCurrent == oldCurrent.t;
    assert newCurrent.Contents[newRemaining] == oldCurrent.Contents[[true] + newRemaining];
    assert [true] + newRemaining == oldRemaining;
  } else {
    assert newCurrent == oldCurrent.f;
    assert newCurrent.Contents[newRemaining] == oldCurrent.Contents[[false] + newRemaining];
    assert [false] + newRemaining == oldRemaining;
  }
}
// </vc-helpers>

method Eval(s: seq<bool>) returns(b: bool)
      requires valid() && |s| == n
      ensures b == Contents[s]
// </vc-spec>
// <vc-code>
{
  var current := root;
  var remaining := s;
  
  while current.n > 0
    invariant current.valid()
    invariant |remaining| == current.n
    invariant current in Repr
    invariant remaining == s[n - current.n..]
    decreases current.n
  {
    var oldCurrent := current;
    var oldRemaining := remaining;
    var bit := remaining[0];
    
    if bit {
      current := current.t;
      remaining := remaining[1..];
    } else {
      current := current.f;
      remaining := remaining[1..];
    }
    
    StepLemma(oldCurrent, current, oldRemaining, remaining, s);
  }
  
  EvalLemma(current, remaining, s);
  b := current.b;
}
// </vc-code>

}