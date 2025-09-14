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
/* helper modified by LLM (iteration 5): Removed unnecessary helper - implementation doesn't need it */
// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Initialize result to a[0] to establish invariant */
    result := a[0];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> result <= a[k]
        invariant i > 0 ==> exists k :: 0 <= k < i && result == a[k]
        invariant i == 0 ==> result == a[0]
    {
        if result > a[i] {
            result := a[i];
        }
        i := i + 1;
    }
}
// </vc-code>
