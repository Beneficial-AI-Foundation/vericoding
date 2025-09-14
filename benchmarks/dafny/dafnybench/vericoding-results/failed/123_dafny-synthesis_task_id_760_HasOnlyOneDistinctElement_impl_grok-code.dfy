

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
  if a.Length == 0 {
    result := true;
  } else {
    result := true;
    var first := a[0];
    var i := 1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant result ==> forall k :: 0 <= k < i ==> a[k] == first
      invariant !result ==> exists k :: 0 <= k < i && a[k] != first
    {
      if a[i] != first {
        result := false;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

