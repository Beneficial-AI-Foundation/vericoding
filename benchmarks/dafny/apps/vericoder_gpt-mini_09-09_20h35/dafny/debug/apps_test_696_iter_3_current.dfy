predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
predicate Good(p: int, i: int) {
    1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))
}

lemma UpdateCountMaintainsInvariant(p:int, i:int, count:int, ok:bool)
    requires ValidInput(p)
    requires 1 <= i <= p-2
    requires count == |set x | 1 <= x < i && Good(p,x)|
    requires ok == (forall k :: 2 <= k <= i ==> !((p-1) % k == 0 && i % k == 0))
    ensures (if ok then count + 1 else count) == |set x | 1 <= x < i+1 && Good(p,x)|
{
    var S: set<int> := set x | 1 <= x < i && Good(p,x);
    var T: set<int> := if Good(p,i) then {i} else {};
    // membership splitting: for any t, t < i+1 iff (t < i) or (t == i)
    assert forall t :: (1 <= t < i+1 && Good(p,t)) <==> (t in S || t in T);
    assert (set x | 1 <= x < i+1 && Good(p,x)) == S + T;
    // the two parts are disjoint because x < i and x == i cannot both hold
    assert forall t :: (t in S && t in T) ==> false;
    // cardinality of union equals sum of cardinalities for disjoint sets
    assert |S + T| == |S| + |T|;
    assert |T| == (if Good(p,i) then 1 else 0);
    assert ok == Good(p,i);
    assert count == |S|;
    assert (if ok then count + 1 else count) == |S| + (if Good(p,i) then 1 else 0);
    assert (if ok then count + 1 else count) == |S + T|;
    assert (if ok then count + 1 else count) == |set x | 1 <= x < i+1 && Good(p,x)|;
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
  if p == 2 {
    return 1;
  }
  var count := 0;
  var i := 1;
  // iterate i over 1 .. p-2
  while i <= p-2
    invariant 1 <= i <= p-1
    invariant count == |set x | 1 <= x < i && Good(p,x)|
    decreases p - i
  {
    var ok := true;
    var j := 2;
    // check if there exists a common divisor j in 2..i
    while j <= i
      invariant 2 <= j <= i+1
      invariant ok == (forall k :: 2 <= k < j ==> !((p-1) % k == 0 && i % k == 0))
      decreases i - j + 1
    {
      if (p-1) % j == 0 && i % j == 0 {
        ok := false;
      }
      j := j + 1;
    }
    // at loop exit j == i+1, so ok == forall k :: 2 <= k <= i ==> ...
    assert ok == (forall k :: 2 <= k <= i ==> !((p-1) % k == 0 && i % k == 0));
    // use lemma to show how count should change to maintain the invariant after i increases
    UpdateCountMaintainsInvariant(p, i, count, ok);
    if ok {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

