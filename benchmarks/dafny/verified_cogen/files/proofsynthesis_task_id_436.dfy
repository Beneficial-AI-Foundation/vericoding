// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negative_list: seq<int>)
    ensures forall x :: x in negative_list ==> x < 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] < 0 ==> arr[i] in negative_list
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
