// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
// </vc-spec>
// <vc-code>
{
    var i: nat := 1;
    max := a[0];
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    invariant exists j :: 0 <= j < i && a[j] == max
    {
        if (a[i] > max) {
            max := a[i];
        }
        i := i + 1;
    }
}
// </vc-code>
