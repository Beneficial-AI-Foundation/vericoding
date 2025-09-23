// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Minimum(a: array<int>) returns (m: int) 
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && m == a[i]
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
// </vc-spec>
// <vc-code>
{
    var n := 0;
    m := a[0];
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant exists i :: 0 <= i < a.Length && m == a[i]
        invariant forall i :: 0 <= i < n ==> m <= a[i]
    {
        if a[n] < m {
            m := a[n];
        }
        n := n + 1;
    }
}
// </vc-code>
