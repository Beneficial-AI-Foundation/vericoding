// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed syntax error in ensures clause and simplified helper approach */
function product(a: array<int>, from: int, to: int): int
    requires 0 <= from <= to < a.Length
    decreases to - from
{
    if from == to then a[from] else a[from] * product(a, from+1, to)
}
// </vc-helpers>

// <vc-spec>
method CumProd(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 0 < i < a.Length ==> result[i] == result[i-1] * a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Simplified implementation using direct computation */
{
    result := new int[a.Length];
    result[0] := a[0];
    var i: int := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant result.Length == a.Length
        invariant result[0] == a[0]
        invariant forall j :: 0 < j < i ==> result[j] == result[j-1] * a[j]
    {
        result[i] := result[i-1] * a[i];
        i := i + 1;
    }
}
// </vc-code>
