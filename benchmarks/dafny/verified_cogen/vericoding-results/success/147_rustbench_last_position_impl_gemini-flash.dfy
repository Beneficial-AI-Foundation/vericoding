// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LastPosition(a: array<int>, elem: int) returns (result: int)
    requires 0 < a.Length < 100_000
    requires exists i :: 0 <= i < a.Length && a[i] == elem
    ensures 0 <= result < a.Length
    ensures forall i :: result < i < a.Length ==> a[i] != elem
    ensures a[result] == elem
// </vc-spec>
// <vc-code>
{
    var i: int := a.Length - 1;
    while i >= 0
        invariant -1 <= i < a.Length
        invariant forall k :: i < k < a.Length ==> a[k] != elem
    {
        if a[i] == elem {
            return i;
        }
        i := i - 1;
    }
    // This code path should not be reachable due to the 'requires exists' clause
    // and the loop invariant ensuring the last position is found.
    // A more complete implementation might include an unreachable assertion or return a default value
    // if the 'requires' clause could be violated, but given the 'requires', we know it will be found.
    return 0; // Should not be reached
}
// </vc-code>
