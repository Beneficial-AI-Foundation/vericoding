// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !result ==> forall k, j :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
    invariant result ==> exists k, j :: 0 <= k < a.Length && 0 <= j < b.Length && a[k] == b[j]
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant !result ==> forall k :: 0 <= k < j ==> a[i] != b[k]
      invariant !result ==> forall k, m :: 0 <= k < i && 0 <= m < b.Length ==> a[k] != b[m]
      invariant result ==> exists k, m :: 0 <= k < a.Length && 0 <= m < b.Length && a[k] == b[m]
    {
      if a[i] == b[j] {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
