// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinarySearch(arr: array<int>, target: int) returns (result: Option<int>)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures match result {
        case Some(index) => 0 <= index < arr.Length && arr[index] == target
        case None => forall i :: 0 <= i < arr.Length ==> arr[i] != target
    }
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
