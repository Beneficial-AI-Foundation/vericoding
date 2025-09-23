// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SmallestListLength(list: array<array<int>>) returns (min: int)
    requires list.Length > 0
    ensures min >= 0
    ensures forall i :: 0 <= i < list.Length ==> min <= list[i].Length
    ensures exists i :: 0 <= i < list.Length && min == list[i].Length
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
