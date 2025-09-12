// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ListDeepClone(arr: array<int>) returns (copied: array<int>)
    ensures arr.Length == copied.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == copied[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
