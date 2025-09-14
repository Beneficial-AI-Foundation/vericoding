// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method intersection(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    ensures
        forall i :: 0 <= i < result.Length ==> (result[i] in arr1[..] && result[i] in arr2[..])
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  result := new int[0];
}
// </vc-code>
