// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPairwiseEqual(a: array<int>) reads a { forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j] }
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  result := forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j];
}
// </vc-code>
