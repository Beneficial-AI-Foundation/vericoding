// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MergeSortedLists(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires 
        forall i, j :: 0 <= i < j < arr1.Length ==> arr1[i] <= arr1[j]
    requires
        forall i, j :: 0 <= i < j < arr2.Length ==> arr2[i] <= arr2[j]
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        result.Length == arr1.Length + arr2.Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause for termination */
    result := new int[arr1.Length + arr2.Length];
    var i := 0;
    var j := 0;
    var k := 0;
    
    while i < arr1.Length || j < arr2.Length
        invariant 0 <= i <= arr1.Length
        invariant 0 <= j <= arr2.Length
        invariant k == i + j
        invariant k <= result.Length
        invariant forall x, y :: 0 <= x < y < k ==> result[x] <= result[y]
        invariant forall x :: 0 <= x < k && i < arr1.Length ==> result[x] <= arr1[i]
        invariant forall x :: 0 <= x < k && j < arr2.Length ==> result[x] <= arr2[j]
        decreases arr1.Length + arr2.Length - i - j
    {
        if i >= arr1.Length {
            result[k] := arr2[j];
            j := j + 1;
        } else if j >= arr2.Length {
            result[k] := arr1[i];
            i := i + 1;
        } else if arr1[i] <= arr2[j] {
            result[k] := arr1[i];
            i := i + 1;
        } else {
            result[k] := arr2[j];
            j := j + 1;
        }
        k := k + 1;
    }
}
// </vc-code>
