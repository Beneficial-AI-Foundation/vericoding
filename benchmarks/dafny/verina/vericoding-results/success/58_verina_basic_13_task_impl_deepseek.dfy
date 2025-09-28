// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed duplicate method implementation */
// </vc-helpers>

// <vc-spec>
method CubeElements(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): using helper-free implementation with loop */
{
    result := new int[a.Length];
    var index := 0;
    while index < a.Length
        decreases a.Length - index
        invariant 0 <= index <= a.Length
        invariant result.Length == a.Length
        invariant forall j :: 0 <= j < index ==> result[j] == a[j] * a[j] * a[j]
    {
        result[index] := a[index] * a[index] * a[index];
        index := index + 1;
    }
}
// </vc-code>
