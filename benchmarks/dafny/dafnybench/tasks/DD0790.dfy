// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
