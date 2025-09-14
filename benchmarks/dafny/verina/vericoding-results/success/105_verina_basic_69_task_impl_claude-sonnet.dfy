// <vc-preamble>
method LinearSearchAux(a: array<int>, e: int, n: nat) returns (result: nat)
    requires n <= a.Length
    decreases a.Length - n
{
    if n < a.Length {
        if a[n] == e {
            result := n;
        } else {
            result := LinearSearchAux(a, e, n + 1);
        }
    } else {
        result := 0;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add stronger specification to LinearSearchAux with existence requirement */
method LinearSearchAuxWithFound(a: array<int>, e: int, n: nat) returns (result: nat)
    requires n <= a.Length
    requires exists i :: n <= i < a.Length && a[i] == e
    ensures result < a.Length
    ensures a[result] == e
    ensures forall k :: n <= k < result ==> a[k] != e
    decreases a.Length - n
{
    if n < a.Length {
        if a[n] == e {
            result := n;
        } else {
            result := LinearSearchAuxWithFound(a, e, n + 1);
        }
    } else {
        assert false;
        result := 0;
    }
}
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (result: nat)
    requires exists i :: 0 <= i < a.Length && a[i] == e
    ensures result < a.Length
    ensures a[result] == e
    ensures forall k :: 0 <= k < result ==> a[k] != e
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use stronger auxiliary method that guarantees finding element */
    result := LinearSearchAuxWithFound(a, e, 0);
}
// </vc-code>
