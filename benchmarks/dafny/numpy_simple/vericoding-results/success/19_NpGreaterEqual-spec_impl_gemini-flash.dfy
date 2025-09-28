// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed syntax for function body */
function GreaterEqualElement(x: int, y: int): bool {
    (x >= y)
}
// </vc-helpers>

// <vc-spec>
method GreaterEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (a[i] >= b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented logic for GreaterEqual method */
{
    result := new bool[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result.Length == a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == (a[j] >= b[j])
    {
        result[i] := GreaterEqualElement(a[i], b[i]);
        i := i + 1;
    }
    return result;
}
// </vc-code>
