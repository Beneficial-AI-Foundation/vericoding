// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
            result := lst[0];
            for i := 1 to lst.Length
                invariant 1 <= i <= lst.Length
                invariant exists j :: 0 <= j < i && lst[j] == result
                invariant forall j :: 0 <= j < i ==> lst[j] <= result
            {
                result := max(result, lst[i]);
            }
        }
// </vc-code>
