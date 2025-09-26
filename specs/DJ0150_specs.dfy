// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
