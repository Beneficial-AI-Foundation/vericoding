// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Deli(a: array<char>, i: nat)
modifies a
requires a.Length > 0
requires 0 <= i < a.Length
ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
// </vc-spec>
// <vc-code>
{
    var c := i;
    while c < a.Length - 1
    invariant i <= c <= a.Length - 1
    invariant forall j :: i <= j < c ==> a[j] == old(a[j + 1])
    // unchanged first half
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
    invariant forall j :: c <= j < a.Length ==> a[j] == old(a[j])
    {
        a[c] := a[c + 1];
        c := c + 1;
    }
    a[c] := '.';
}
// </vc-code>
