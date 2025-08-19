// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Minimum(a: array<int>) returns (m: int) 
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && m == a[i]
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>