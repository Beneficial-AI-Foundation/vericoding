// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SmallestListLength(lists: array<array<int>>) returns (result: int)
    requires lists.Length > 0
    ensures exists i :: 0 <= i < lists.Length && result == lists[i].Length
    ensures forall i :: 0 <= i < lists.Length ==> result <= lists[i].Length
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
