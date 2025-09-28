// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (even_numbers: seq<int>)
    ensures |even_numbers| <= arr.Length
    ensures forall i :: 0 <= i < |even_numbers| ==> even_numbers[i] % 2 == 0
    ensures forall x :: x in even_numbers ==> x in arr[..]
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> arr[i] in even_numbers
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Strengthened loop invariants and postconditions for correctness. */
{
    var temp_even_numbers: seq<int> := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |temp_even_numbers| ==> temp_even_numbers[j] % 2 == 0
        invariant forall x :: x in temp_even_numbers ==> x in arr[..]
        invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> arr[k] in temp_even_numbers
        invariant forall k :: 0 <= k < i && arr[k] % 2 != 0 ==> arr[k] !in temp_even_numbers
        invariant |temp_even_numbers| <= i
    {
        if arr[i] % 2 == 0 {
            temp_even_numbers := temp_even_numbers + [arr[i]];
        }
        i := i + 1;
    }
    even_numbers := temp_even_numbers;
}
// </vc-code>
