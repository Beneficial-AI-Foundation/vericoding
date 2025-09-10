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
    1 <= i < p-1 && (forall j {:trigger j} :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))
}

function CountUpTo(p:int, i:int): int
    requires ValidInput(p)
{
    if i <= 1 then 0 else |set x | 1 <= x < i && Good(p,x)|
}

lemma UpdateCountMaintainsInvariant(p:int, i:int, count:int, ok:bool)
    requires ValidInput(p)
    requires 1 <= i <= p-2
    requires count == CountUpTo(p,i)
    requires ok == (forall k :: 2 <= k <= i ==> !((p-1) % k == 0 && i % k == 0))
    ensures (if ok then count + 1 else count) == CountUpTo(p,i+1)
{
    var S: set<int> := set x | 1 <= x < i && Good(p,x);
    var T: set<int> := if Good(p,i) then {i} else {};
    // Unfold CountUpTo for i and i+1 (i >= 1 so i> =1; for i==1 CountUpTo returns 0 and S is empty)
    assert CountUpTo(p,i) == |S|;
    assert CountUpTo(p,i+1) == |set x | 1 <= x < i+1 && Good(p,x)|;
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
    assert (if ok then count + 1 else count) == CountUpTo(p,i+1);
}

lemma CountUpTo_pminus1_equals(p:int)
    requires ValidInput(p)
    requires p != 2
    ensures CountUpTo(p,p-1) == CountPrimitiveRoots(p)
{
    // Unfold CountUpTo for the relevant arguments
    assert CountUpTo(p,p-1) == |set x | 1 <= x < p-1 && Good(p,x)|;

    // Unfold CountPrimitiveRoots to its definition form (uses the explicit quantifier);
    // the trigger on Good's quantifier ensures the equivalence between the two set comprehensions.
    assert CountPrimitiveRoots(p) == (if p == 2 then 1 else |set i | 1 <= i < p-1 && (forall j {:trigger j} :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)));
    assert p != 2;
    // Good(p,x) is defined to be 1 <= x < p-1 && (forall j :: ...), so the two set comprehensions are extensionally equal.
    assert forall x :: (1 <= x < p-1 && Good(p,x)) <==> (1 <= x < p-1 && (forall j {:trigger j} :: 2 <= j <= x ==> !((p-1) % j == 0 && x % j == 0)));
    assert |set x | 1 <= x < p-1 && Good(p,x)| == |set i | 1 <= i < p-1 && (forall j {:trigger j} :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|;
    assert CountUpTo(p,p-1) == CountPrimitiveRoots(p);
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
    invariant count == CountUpTo(p,i)
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
  // After loop exit i == p-1
  assert i == p-1;
  assert count == CountUpTo(p,p-1);
  CountUpTo_pminus1_equals(p);
  assert count == CountPrimitiveRoots(p);
  return count;
}
// </vc-code>

