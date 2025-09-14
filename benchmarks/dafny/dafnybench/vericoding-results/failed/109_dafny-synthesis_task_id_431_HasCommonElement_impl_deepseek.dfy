

// <vc-helpers>
lemma CommonElementExists(a: array<int>, b: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < b.Length
  requires a[i] == b[j]
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
{
}

lemma NoCommonElementInRow(a: array<int>, b: array<int>, i: int)
  requires 0 <= i < a.Length
  requires forall j :: 0 <= j < b.Length ==> a[i] != b[j]
  ensures forall k, j :: 0 <= k <= i && 0 <= j < b.Length ==> a[k] != b[j]
{
  var k: int, j: int := 0, 0;
  while k <= i
    invariant 0 <= k <= i+1
    invariant forall x, y :: 0 <= x < k && 0 <= y < b.Length ==> a[x] != b[y]
  {
    if k < i {
      // k is less than i, so we already know a[k] != b[j] for all j
      k := k + 1;
    } else if k == i {
      // At current row i, we know a[i] != b[j] for all j by precondition
      k := k + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !result ==> forall k, j :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
  {
    var j := 0;
    var found := false;
    
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant !found ==> forall k :: 0 <= k < j ==> a[i] != b[k]
      invariant found ==> exists k :: 0 <= k < j && a[i] == b[k]
    {
      if a[i] == b[j] {
        found := true;
        result := true;
        CommonElementExists(a, b, i, j);
        break;
      }
      j := j + 1;
    }
    
    if !found {
      NoCommonElementInRow(a, b, i);
    }
    
    i := i + 1;
  }
}
// </vc-code>

