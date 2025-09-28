// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original error was related to an insufficient reads clause for accessing array elements within the helper product function. The fix is to add 'reads a' to the product function's signature, allowing it to properly read elements from the input array 'a'. This resolves the 'insufficient reads clause' compilation error. */
function {:pure} product(a: array<int>, i: int): int
    reads a
    requires 0 <= i < a.Length
{
    if i == 0 then a[0] else product(a, i-1) * a[i]
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
/* code modified by LLM (iteration 2): The previous code had a verification error in the postcondition related to result[0] == a[0]. The fix acknowledges that this is correctly handled by the explicit assignment 'result[0] := a[0];'. The loop invariants correctly preserve this property during the cumulative product calculation. */
{
    result := new int[a.Length];
    result[0] := a[0];
    var i := 1;
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
