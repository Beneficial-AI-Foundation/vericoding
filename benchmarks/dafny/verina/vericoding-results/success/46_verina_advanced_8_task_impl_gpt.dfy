// <vc-preamble>
function CalculateAcc(gas: array<int>, cost: array<int>, start: int, steps: int): int
    requires gas.Length == cost.Length
    requires gas.Length > 0
    requires 0 <= start < gas.Length
    reads gas, cost
    decreases steps
{
    if steps <= 0 then
        0
    else
        var prev_acc := CalculateAcc(gas, cost, start, steps - 1);
        var jdx := ((start + (steps - 1)) % gas.Length) % gas.Length;
        prev_acc + gas[jdx] - cost[jdx]
}

predicate ValidStartingPoint(gas: array<int>, cost: array<int>, start: int)
    requires gas.Length == cost.Length
    requires gas.Length > 0
    reads gas, cost
{
    0 <= start < gas.Length && 
    forall i {:trigger CalculateAcc(gas, cost, start, i + 1)} :: 0 <= i < gas.Length ==> CalculateAcc(gas, cost, start, i + 1) >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Lemma showing a start is invalid if some prefix accumulation is negative */
lemma NotValidIfExistsNegative(gas: array<int>, cost: array<int>, start: int, i: int)
    requires gas.Length == cost.Length
    requires gas.Length > 0
    requires 0 <= start < gas.Length
    requires 0 <= i < gas.Length
    requires CalculateAcc(gas, cost, start, i + 1) < 0
    ensures !ValidStartingPoint(gas, cost, start)
{
    assert !(forall k {:trigger CalculateAcc(gas, cost, start, k + 1)} :: 0 <= k < gas.Length ==> CalculateAcc(gas, cost, start, k + 1) >= 0) by {
        assert 0 <= i < gas.Length;
        assert !(CalculateAcc(gas, cost, start, i + 1) >= 0);
    }
    assert !ValidStartingPoint(gas, cost, start);
}
// </vc-helpers>

// <vc-spec>
method CanCompleteCircuit(gas: array<int>, cost: array<int>) returns (result: int)
    requires gas.Length == cost.Length
    requires gas.Length > 0
    ensures (result == -1) ==> (forall start :: 0 <= start < gas.Length ==> !ValidStartingPoint(gas, cost, start))
    ensures (result >= 0) ==> (
        0 <= result < gas.Length &&
        ValidStartingPoint(gas, cost, result) &&
        (forall start :: 0 <= start < result ==> !ValidStartingPoint(gas, cost, start))
    )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Linear scan; inner loop checks prefix sums using CalculateAcc; structured to ensure termination */
  var n := gas.Length;
  var s := 0;
  result := -1;
  while s < n
    invariant 0 <= s <= n
    invariant result == -1
    invariant forall start :: 0 <= start < s ==> !ValidStartingPoint(gas, cost, start)
    decreases n - s
  {
    var i := 0;
    var ok := true;
    var haveWitness := false;
    var witnessI := 0;
    while i < n
      invariant 0 <= i <= n
      invariant 0 <= s < n
      invariant ok ==> (forall k {:trigger CalculateAcc(gas, cost, s, k + 1)} :: 0 <= k < i ==> CalculateAcc(gas, cost, s, k + 1) >= 0)
      invariant haveWitness ==> (0 <= witnessI < n && CalculateAcc(gas, cost, s, witnessI + 1) < 0)
      invariant (!ok) ==> haveWitness
      decreases n - i
    {
      var acc := CalculateAcc(gas, cost, s, i + 1);
      if acc < 0 {
        witnessI := i;
        haveWitness := true;
        ok := false;
        i := n;
      } else {
        i := i + 1;
      }
    }
    if ok {
      assert i == n;
      assert forall k {:trigger CalculateAcc(gas, cost, s, k + 1)} :: 0 <= k < n ==> CalculateAcc(gas, cost, s, k + 1) >= 0;
      assert ValidStartingPoint(gas, cost, s);
      result := s;
      return;
    } else {
      assert haveWitness;
      NotValidIfExistsNegative(gas, cost, s, witnessI);
      s := s + 1;
    }
  }
  assert forall start :: 0 <= start < n ==> !ValidStartingPoint(gas, cost, start);
  result := -1;
}
// </vc-code>
