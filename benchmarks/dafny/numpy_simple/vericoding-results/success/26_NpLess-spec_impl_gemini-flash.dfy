// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Less(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] < b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed index out of bounds error in loop where upper bound was a.Length - 1, and added loop invariant */
{
    result := new bool[a.Length];
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> result[k] == (a[k] < b[k])
    {
        if i < a.Length {
            result[i] := a[i] < b[i];
        }
    }
}
// </vc-code>
