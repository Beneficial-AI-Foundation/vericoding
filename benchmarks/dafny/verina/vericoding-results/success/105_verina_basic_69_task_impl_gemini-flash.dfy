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
    result := 0;
    while result < a.Length
        invariant 0 <= result <= a.Length
        invariant forall k :: 0 <= k < result ==> a[k] != e
        decreases a.Length - result
    {
        if a[result] == e {
            return;
        }
        result := result + 1;
    }
    // This point should not be reached due to the `requires` clause.
    // However, if it were, we'd need to handle it. For now, the loop ensures the postconditions.
}
// </vc-code>
