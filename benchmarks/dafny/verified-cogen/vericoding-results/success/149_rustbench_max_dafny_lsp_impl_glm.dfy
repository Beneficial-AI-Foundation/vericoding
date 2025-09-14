// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified helper to track max value directly */
function maxIndex(a: array<int>, i: int, j: int): int 
    reads a
    requires 0 <= i < a.Length && 0 <= j < a.Length
{
    if a[i] > a[j] then i else j
}
// </vc-helpers>

// <vc-spec>
method MaxDafnyLsp(a: array<int>) returns (x: int)
    requires a.Length > 0
    ensures 0 <= x < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[x]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added invariant i <= a.Length to fix index out of range */
    x := 0;
    var i := 1;
    while i < a.Length
        invariant 0 <= x < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] <= a[x]
    {
        if a[i] > a[x] {
            x := i;
        }
        i := i + 1;
    }
}
// </vc-code>
