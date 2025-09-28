// <vc-preamble>
predicate IsNonZeroVector(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>
lemma NonZeroArrayElems(b: array<int>)
    requires IsNonZeroVector(b[..])
    ensures forall i :: 0 <= i < b.Length ==> b[i] != 0
{
    var n := b.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> b[j] != 0
    {
        assert b[..][i] != 0;
        assert b[i] == b[..][i];
        assert b[i] != 0;
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method FloorDivide(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires IsNonZeroVector(b[..])
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] / b[i]
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    result := new int[n];
    NonZeroArrayElems(b);
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result.Length == n
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
    {
        result[i] := a[i] / b[i];
        i := i + 1;
    }
}
// </vc-code>
