// <vc-preamble>
predicate IsNonZeroVector(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): fix array initialization with explicit loop */
  result := new int[a.Length];
  for i := 0 to a.Length
  invariant 0 <= i <= a.Length
  invariant forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
  {
    result[i] := a[i] / b[i];
  }
}
// </vc-code>
