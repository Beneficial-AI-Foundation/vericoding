// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added reads clauses */
predicate EqualAt(a: array<int>, b: array<int>, i: int)
    requires 0 <= i < a.Length
    requires a.Length == b.Length
    reads a, b
{
    a[i] == b[i]
}
// </vc-helpers>

// <vc-spec>
method Equal(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (a[i] == b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed after helper fix */
{
    var result_arr := new bool[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result_arr.Length == a.Length
        invariant forall j :: 0 <= j < i ==> result_arr[j] == (a[j] == b[j])
    {
        result_arr[i] := (a[i] == b[i]);
        i := i + 1;
    }
    return result_arr;
}
// </vc-code>
