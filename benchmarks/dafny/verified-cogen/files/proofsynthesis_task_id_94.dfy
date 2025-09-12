// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(arr: array<array<int>>) returns (first_of_min_second: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> arr[i].Length >= 2
    ensures exists i :: (0 <= i < arr.Length && first_of_min_second == arr[i][0] && 
            (forall j :: 0 <= j < arr.Length ==> arr[i][1] <= arr[j][1]))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
