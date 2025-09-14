// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  result := true;
  if a.Length > 1 {
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant result ==> (forall k :: 1 <= k < i ==> a[k] == a[0])
    {
      if a[i] != a[0] {
        result := false;
        return;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
