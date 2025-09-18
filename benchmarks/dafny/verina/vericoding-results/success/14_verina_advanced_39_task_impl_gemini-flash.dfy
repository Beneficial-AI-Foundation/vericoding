// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: nat, b: nat): nat {
    if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<nat>) returns (result: nat)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
{
    result := lst[0];
    var i := 1;
    while i < lst.Length
        invariant 0 < i <= lst.Length
        invariant exists k :: 0 <= k < i && lst[k] == result
        invariant forall k :: 0 <= k < i ==> lst[k] <= result
    {
        result := Max(result, lst[i]);
        i := i + 1;
    }
}
// </vc-code>
