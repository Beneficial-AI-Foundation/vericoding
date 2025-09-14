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
/* helper modified by LLM (iteration 5): Simplified proof without redundant double modulo */
lemma CalculateAccMonotonic(gas: array<int>, cost: array<int>, start: int, steps1: int, steps2: int)
    requires gas.Length == cost.Length
    requires gas.Length > 0
    requires 0 <= start < gas.Length
    requires 0 <= steps1 <= steps2
    ensures CalculateAcc(gas, cost, start, steps2) >= CalculateAcc(gas, cost, start, steps1)
{
    var k := steps1;
    while k < steps2
        invariant steps1 <= k <= steps2
        invariant CalculateAcc(gas, cost, start, k) >= CalculateAcc(gas, cost, start, steps1)
    {
        k := k + 1;
    }
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
/* code modified by LLM (iteration 5): Simplified validation without nested loops */
{
    result := -1;
    var i := 0;
    while i < gas.Length
        invariant 0 <= i <= gas.Length
        invariant result == -1 ==> forall start :: 0 <= start < i ==> !ValidStartingPoint(gas, cost, start)
        invariant result >= 0 ==> (0 <= result < gas.Length && ValidStartingPoint(gas, cost, result) && forall start :: 0 <= start < result ==> !ValidStartingPoint(gas, cost, start))
    {
        var isValid := true;
        var acc := 0;
        var j := 0;
        while j < gas.Length && isValid
            invariant 0 <= j <= gas.Length
            invariant isValid ==> acc >= 0
            invariant isValid ==> forall k :: 0 <= k < j ==> CalculateAcc(gas, cost, i, k + 1) >= 0
        {
            var idx := (i + j) % gas.Length;
            acc := acc + gas[idx] - cost[idx];
            if acc < 0 {
                isValid := false;
            }
            j := j + 1;
        }
        if isValid {
            result := i;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
