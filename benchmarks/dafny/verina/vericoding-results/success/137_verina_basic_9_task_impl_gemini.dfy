// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed syntax by removing 'method' keyword from function declaration */
function IsIn(val: int, arr: array<int>): bool
    reads arr
{
    val in arr[..]
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
{
    /* code modified by LLM (iteration 2): no change, logic is sound pending helper compilation fix */
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> !IsIn(a[k], b)
    {
        if IsIn(a[i], b) {
            result := true;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
