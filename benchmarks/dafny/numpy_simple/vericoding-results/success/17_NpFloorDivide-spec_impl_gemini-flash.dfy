// <vc-preamble>
predicate IsNonZeroVector(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>
function FloorDivision(numerator: int, denominator: int): int
    requires denominator != 0
    ensures (numerator / denominator) == FloorDivision(numerator, denominator)
{
    numerator / denominator
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
    result := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == FloorDivision(a[j], b[j])
    {
        result[i] := FloorDivision(a[i], b[i]);
        i := i + 1;
    }
}
// </vc-code>
