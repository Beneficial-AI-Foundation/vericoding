// <vc-preamble>
function LoopSpec(a: array<int>, i: int, currentMin: int): int
    requires 0 <= i <= a.Length
    decreases a.Length - i
    reads a
{
    if i < a.Length then
        var newMin := if currentMin > a[i] then a[i] else currentMin;
        LoopSpec(a, i + 1, newMin)
    else
        currentMin
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
