// <vc-preamble>
predicate IsNonZeroVector(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>

predicate AllIndicesValidForDivision(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  requires IsNonZeroVector(b)
{
  forall i :: 0 <= i < |a| ==> b[i] != 0
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
  var idx: int := 0;
  while idx < a.Length
    invariant 0 <= idx <= a.Length
    invariant forall j :: 0 <= j < idx ==> result[j] == a[j] / b[j]
  {
    result[idx] := a[idx] / b[idx];
    idx := idx + 1;
  }
}
// </vc-code>
