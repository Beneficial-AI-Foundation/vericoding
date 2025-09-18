// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array access */
predicate existsInArray(arr: array<int>, val: int)
    reads arr
{
    exists k :: 0 <= k < arr.Length && arr[k] == val
}
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop invariant to refer to the correct indices and ensure correctness */
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> (forall j :: 0 <= j < b.Length ==> a[k] != b[j])
        decreases a.Length - i
    {
        if existsInArray(b, a[i]) {
            return true;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>
