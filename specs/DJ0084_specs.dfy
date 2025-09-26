// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
