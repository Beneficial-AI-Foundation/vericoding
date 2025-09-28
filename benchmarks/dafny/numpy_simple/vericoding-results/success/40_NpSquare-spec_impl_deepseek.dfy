// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function square(x: int): int
{
    x * x
}

// </vc-helpers>

// <vc-spec>
method Square(arr: array<int>) returns (result: array<int>)
    ensures
        result.Length == arr.Length &&
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
// </vc-spec>
// <vc-code>
{
    result := new int[arr.Length];
    var idx := 0;
    while idx < arr.Length
        invariant 0 <= idx <= arr.Length
        invariant forall i :: 0 <= i < idx ==> result[i] == arr[i] * arr[i]
    {
        result[idx] := arr[idx] * arr[idx];
        idx := idx + 1;
    }
}
// </vc-code>
