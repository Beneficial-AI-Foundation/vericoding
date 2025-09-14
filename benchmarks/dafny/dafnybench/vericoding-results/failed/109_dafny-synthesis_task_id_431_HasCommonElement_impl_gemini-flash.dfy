

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
  var i := 0;
  var found := false;
  while i < a.Length && !found
    invariant 0 <= i <= a.Length
    invariant !found ==> (forall i_a :: 0 <= i_a < i ==> (forall j_b :: 0 <= j_b < b.Length ==> a[i_a] != b[j_b]))
    invariant found ==> (exists i_a, j_b :: 0 <= i_a < i && 0 <= j_b < b.Length && a[i_a] == b[j_b])
  {
    var j := 0;
    while j < b.Length && !found
      invariant 0 <= j <= b.Length
      invariant 0 <= i < a.Length // Added invariant
      invariant !found ==> (forall i_a :: 0 <= i_a < i ==> (forall j_b :: 0 <= j_b < b.Length ==> a[i_a] != b[j_b])) &&
                           (forall j_b :: 0 <= j_b < j ==> a[i] != b[j_b])
      invariant found ==> (exists i_a, j_b :: 0 <= i_a < i && 0 <= j_b < b.Length && a[i_a] == b[j_b]) ||
                          (exists j_b :: 0 <= j_b < j && a[i] == b[j_b])
    {
      if a[i] == b[j] {
        found := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>

