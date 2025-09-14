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
  if a.Length == 0 {
    result := true;
  } else {
    result := true;
    var first := a[0];
    var i := 1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant result ==> forall j :: 0 <= j < i ==> a[j] == first
      invariant !result ==> exists j :: 0 <= j < i && a[j] != first
    {
      if a[i] != first {
        result := false;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
