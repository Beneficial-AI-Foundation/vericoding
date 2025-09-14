

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    var i: int := 0;
    for i := 0; i < a.Length; i := i + 1
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] % b[j]
    {
        result[i] := a[i] % b[i];
    }
}
// </vc-code>

