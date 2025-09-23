// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveElements(arr1: array<int>, arr2: array<int>) returns (result: seq<int>)
    ensures
        forall i: int ::
            0 <= i < |result| ==> (result[i] in arr1[..] && !(result[i] in arr2[..]))
    ensures
        forall i: int ::
            0 <= i < arr1.Length ==> (arr1[i] in arr2[..] || arr1[i] in result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
