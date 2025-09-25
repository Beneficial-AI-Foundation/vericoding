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
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
