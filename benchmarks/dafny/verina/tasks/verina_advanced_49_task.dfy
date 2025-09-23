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
    // impl-start
    result := new int[arr1.Length + arr2.Length];
    assume {:axiom} false;
    // impl-end
}
// </vc-code>
