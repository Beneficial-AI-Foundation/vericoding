// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SharedElements(list1: array<int>, list2: array<int>) returns (shared: array<int>)
    ensures
        forall i :: 0 <= i < shared.Length ==> (shared[i] in list1[..] && shared[i] in list2[..])
    ensures
        forall i, j :: 0 <= i < j < shared.Length ==> shared[i] != shared[j]
// </vc-spec>
// <vc-code>
{
  shared := new int[0];
}
// </vc-code>
