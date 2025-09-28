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
lemma LoopSpecCorrectness(a: array<int>, i: int, currentMin: int, j: int)
    requires 0 <= i <= a.Length
    requires 0 <= j < a.Length
    requires forall k :: 0 <= k < i ==> currentMin <= a[k]
    requires exists k :: 0 <= k < i && currentMin == a[k]
    ensures LoopSpec(a, i, currentMin) <= a[j]
    decreases a.Length - i
{
    if i < a.Length {
        var newMin := if currentMin > a[i] then a[i] else currentMin;
        LoopSpecCorrectness(a, i + 1, newMin, j);
    }
}

lemma LoopSpecExists(a: array<int>, i: int, currentMin: int)
    requires 0 <= i <= a.Length
    requires forall k :: 0 <= k < i ==> currentMin <= a[k]
    requires exists k :: 0 <= k < i && currentMin == a[k]
    ensures exists k :: 0 <= k < a.Length && LoopSpec(a, i, currentMin) == a[k]
    decreases a.Length - i
{
    if i < a.Length {
        var newMin := if currentMin > a[i] then a[i] else currentMin;
        LoopSpecExists(a, i + 1, newMin);
    }
}

/* helper modified by LLM (iteration 2): added lemma to prove loop invariant maintenance */
lemma LoopSpecInvariant(a: array<int>, i: int, currentMin: int)
    requires 0 <= i < a.Length
    requires forall k :: 0 <= k < i ==> currentMin <= a[k]
    requires exists k :: 0 <= k < i && currentMin == a[k]
    ensures LoopSpec(a, i, currentMin) == LoopSpec(a, i + 1, if currentMin > a[i] then a[i] else currentMin)
{
    var newMin := if currentMin > a[i] then a[i] else currentMin;
    assert LoopSpec(a, i, currentMin) == LoopSpec(a, i + 1, newMin);
}
// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): simplified loop invariant to avoid circular dependency */
    result := a[0];
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result <= a[j]
        invariant exists j :: 0 <= j < i && result == a[j]
    {
        if a[i] < result {
            result := a[i];
        }
        i := i + 1;
    }
}
// </vc-code>
