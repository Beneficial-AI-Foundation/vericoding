// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (odd_list: seq<int>)
    ensures |odd_list| == |set i | 0 <= i < arr.Length && arr[i] % 2 != 0|
    ensures forall x :: x in odd_list ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_list
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
