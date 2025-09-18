// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clauses for termination */
function min(a: nat, b: nat): nat { if a <= b then a else b }

function arrayMin(s: array<nat>, start: nat): nat
    requires s.Length > 0
    requires 0 <= start < s.Length
    reads s
    decreases s.Length - start
{
    if start == s.Length - 1 then s[start]
    else min(s[start], arrayMin(s, start + 1))
}

lemma arrayMinIsSmallest(s: array<nat>, start: nat)
    requires s.Length > 0
    requires 0 <= start < s.Length
    ensures forall i :: start <= i < s.Length ==> arrayMin(s, start) <= s[i]
    ensures exists i :: start <= i < s.Length && s[i] == arrayMin(s, start)
    decreases s.Length - start
{
    if start == s.Length - 1 {
        assert s[start] == arrayMin(s, start);
    } else {
        arrayMinIsSmallest(s, start + 1);
        var minRest := arrayMin(s, start + 1);
        var currentMin := arrayMin(s, start);
        assert currentMin == min(s[start], minRest);
    }
}
// </vc-helpers>

// <vc-spec>
method FindSmallest(s: array<nat>) returns (result: Option<nat>)
    ensures
        match result {
            case None => s.Length == 0
            case Some(r) => s.Length > 0 && 
                      (exists i :: 0 <= i < s.Length && s[i] == r) &&
                      (forall i :: 0 <= i < s.Length ==> r <= s[i])
        }
// </vc-spec>
// <vc-code>
{
    if s.Length == 0 {
        result := None;
    } else {
        var minVal := arrayMin(s, 0);
        arrayMinIsSmallest(s, 0);
        result := Some(minVal);
    }
}
// </vc-code>
