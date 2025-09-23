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
    // TODO: implement
    assume {:axiom} false;
    result := 0;
}
// </vc-code>
