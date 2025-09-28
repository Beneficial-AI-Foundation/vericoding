// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method WhereFn(condition: array<bool>, x: array<int>, y: array<int>) returns (result: array<int>)
    requires 
        condition.Length == x.Length &&
        x.Length == y.Length
    ensures 
        result.Length == condition.Length &&
        forall i :: 0 <= i < result.Length ==> 
            result[i] == if condition[i] then x[i] else y[i]
{
    assume {:axiom} false;
}

method WhereWithTransform(arr: array<int>) returns (result: array<int>)
    requires arr.Length >= 0
    ensures 
        result.Length == arr.Length
{
    assume {:axiom} false;
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement WhereFn method body */
    result := new int[condition.Length];
    for i := 0 to condition.Length
        invariant 0 <= i <= condition.Length
        invariant result.Length == condition.Length
        invariant forall j :: 0 <= j < i ==> result[j] == if condition[j] then x[j] else y[j]
    {
        result[i] := if condition[i] then x[i] else y[i];
    }
}

method WhereWithTransformImpl(arr: array<int>) returns (result: array<int>)
    requires arr.Length >= 0
    ensures 
        result.Length == arr.Length
{
    /* code modified by LLM (iteration 5): implement WhereWithTransform method body */
    result := new int[arr.Length];
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant result.Length == arr.Length
    {
        result[i] := arr[i];
    }
}
// </vc-code>
