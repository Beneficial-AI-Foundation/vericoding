// <vc-preamble>
predicate MaxArrayPrecond(a: array<int>)
{
    a.Length > 0
}
method MaxArrayAux(a: array<int>, index: int, current: int) returns (result: int)
    requires 0 <= index <= a.Length
    decreases a.Length - index
{
    if index < a.Length {
        var new_current := if current > a[index] then current else a[index];
        result := MaxArrayAux(a, index + 1, new_current);
    } else {
        result := current;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): A function needs a reads clause to access the heap. */
function max_array_aux_func(a: array<int>, index: int, current: int): int
    reads a
    requires 0 <= index <= a.Length
    decreases a.Length - index
{
    if index < a.Length then
        var new_current := if current > a[index] then current else a[index];
        max_array_aux_func(a, index + 1, new_current)
    else
        current
}

/* helper modified by LLM (iteration 4): removed reads clause to fix compilation error */
lemma MaxArrayAux_Properties(a: array<int>, index: int, current: int)
    requires 0 <= index <= a.Length
    ensures forall i :: index <= i < a.Length ==> max_array_aux_func(a, index, current) >= a[i]
    ensures max_array_aux_func(a, index, current) >= current
    ensures max_array_aux_func(a, index, current) == current || (exists i :: index <= i < a.Length && max_array_aux_func(a, index, current) == a[i])
    decreases a.Length - index
{
    if index < a.Length {
        var new_current := if current > a[index] then current else a[index];
        MaxArrayAux_Properties(a, index + 1, new_current);
    }
}
// </vc-helpers>

// <vc-spec>
method MaxArray(a: array<int>) returns (result: int)
    requires MaxArrayPrecond(a)
    ensures forall k :: 0 <= k < a.Length ==> result >= a[k]
    ensures exists k :: 0 <= k < a.Length && result == a[k]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): logic relies on corrected helpers */
    MaxArrayAux_Properties(a, 1, a[0]);
    result := max_array_aux_func(a, 1, a[0]);
}
// </vc-code>
