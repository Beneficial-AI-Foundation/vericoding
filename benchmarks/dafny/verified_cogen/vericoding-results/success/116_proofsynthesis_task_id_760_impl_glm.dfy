// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause for termination */
function AllEqualToFirst(arr: array<int>, index: int): bool
    requires 0 <= index <= arr.Length
    reads arr
    decreases arr.Length - index
{
    if index >= arr.Length then
        true
    else
        arr[index] == arr[0] && AllEqualToFirst(arr, index + 1)
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added break when counterexample found */
{
    if arr.Length == 0 {
        result := true;
    } else {
        result := true;
        var i := 1;
        while i < arr.Length
            invariant 1 <= i <= arr.Length
            invariant forall j :: 1 <= j < i ==> arr[j] == arr[0]
        {
            if arr[i] != arr[0] {
                result := false;
                break;
            }
            i := i + 1;
        }
    }
}
// </vc-code>
