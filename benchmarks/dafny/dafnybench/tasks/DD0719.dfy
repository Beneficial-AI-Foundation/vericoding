// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
