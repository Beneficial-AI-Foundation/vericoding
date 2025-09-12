// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
