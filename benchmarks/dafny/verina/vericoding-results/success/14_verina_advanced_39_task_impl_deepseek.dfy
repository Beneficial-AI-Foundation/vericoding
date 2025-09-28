// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: nat, b: nat): nat
{
    if a > b then a else b
}

lemma max_property(a: nat, b: nat)
    ensures max(a, b) >= a
    ensures max(a, b) >= b
    ensures max(a, b) == a || max(a, b) == b
{
}

lemma max_commutative(a: nat, b: nat)
    ensures max(a, b) == max(b, a)
{
}

lemma max_exists(lst: array<nat>, i: int, current_max: nat, k: int)
    requires 0 <= i < lst.Length
    requires 0 <= k < i
    requires lst[k] == current_max
    ensures exists j :: 0 <= j < i && lst[j] == current_max
{
}

lemma max_is_max(lst: array<nat>, i: int, current_max: nat)
    requires 0 <= i <= lst.Length
    requires forall j :: 0 <= j < i ==> lst[j] <= current_max
    ensures forall j :: 0 <= j < i ==> lst[j] <= current_max
{
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
    /* code modified by LLM (iteration 5): Fixed loop invariant with proper tracking of max index */
    var i: int := 1;
    var max_index: int := 0;
    result := lst[0];
    
    while i < lst.Length
        invariant 0 <= i <= lst.Length
        invariant 0 <= max_index < lst.Length
        invariant lst[max_index] == result
        invariant forall j :: 0 <= j < i ==> lst[j] <= result
    {
        if lst[i] > result {
            result := lst[i];
            max_index := i;
        }
        i := i + 1;
    }
}
// </vc-code>
