// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HasCommonElement(list1: array<int>, list2: array<int>) returns (result: bool)
    ensures
        result == (exists i: int, j: int ::
            0 <= i < list1.Length && 0 <= j < list2.Length && (list1[i] == list2[j]))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
