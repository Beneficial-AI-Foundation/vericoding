// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(arr: array<int>, elem: int) returns (result: array<int>)
    ensures
        result.Length == (2 * arr.Length) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k] == elem) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k + 1] == arr[k])
// </vc-spec>
// <vc-code>
{
    result := new int[2 * arr.Length];
    var k := 0;
    while k < arr.Length
        invariant 0 <= k <= arr.Length
        invariant result.Length == 2 * arr.Length
        invariant forall i :: 0 <= i < k ==> result[2 * i] == elem
        invariant forall i :: 0 <= i < k ==> result[2 * i + 1] == arr[i]
    {
        result[2 * k] := elem;
        result[2 * k + 1] := arr[k];
        k := k + 1;
    }
}
// </vc-code>
