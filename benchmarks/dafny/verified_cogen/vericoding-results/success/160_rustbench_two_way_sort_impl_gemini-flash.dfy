// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoWaySort(a: array<bool>)
    requires a.Length <= 100_000
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
    modifies a
// </vc-spec>
// <vc-code>
{
    var left := 0;
    var right := a.Length - 1;

    while left <= right
        invariant 0 <= left <= a.Length
        invariant -1 <= right < a.Length
        invariant forall i :: 0 <= i < left ==> !a[i]
        invariant forall i :: right < i < a.Length ==> a[i]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        if !a[left] {
            left := left + 1;
        } else if a[right] {
            right := right - 1;
        } else {
            // a[left] is true and a[right] is false
            a[left], a[right] := a[right], a[left];
            left := left + 1;
            right := right - 1;
        }
    }
}
// </vc-code>
