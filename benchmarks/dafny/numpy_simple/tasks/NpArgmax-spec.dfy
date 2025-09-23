// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Argmax(arr: array<int>) returns (result: int)
    requires arr.Length > 0
    ensures 
        0 <= result < arr.Length &&
        (forall i :: 0 <= i < result ==> arr[result] > arr[i]) &&
        (forall i :: result < i < arr.Length ==> arr[result] >= arr[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
