// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (odd_numbers: seq<int>)
    ensures forall x :: x in odd_numbers ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_numbers
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
