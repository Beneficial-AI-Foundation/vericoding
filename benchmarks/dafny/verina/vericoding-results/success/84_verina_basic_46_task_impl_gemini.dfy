// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.Length &&
            arr[result] == elem &&
            forall k :: result < k < arr.Length ==> arr[k] != elem) &&
        (result == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
// </vc-spec>
// <vc-code>
{
    result := -1;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result == -1 ==> forall k :: 0 <= k < i ==> arr[k] != elem
        invariant result >= 0 ==> 0 <= result < i && arr[result] == elem &&
                                   forall k :: result < k < i ==> arr[k] != elem
    {
        if arr[i] == elem {
            result := i;
        }
        i := i + 1;
    }
}
// </vc-code>
