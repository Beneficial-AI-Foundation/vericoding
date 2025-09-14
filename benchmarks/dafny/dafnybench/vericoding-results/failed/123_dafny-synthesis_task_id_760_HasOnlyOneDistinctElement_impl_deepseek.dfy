

// <vc-helpers>
lemma FindDistinctPair(a: array<int>) returns (i: int, j: int)
  requires a != null
  requires a.Length > 0
  ensures (0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]) || 
          (forall k, l :: 0 <= k < a.Length && 0 <= l < a.Length ==> a[k] == a[l])
{
  if a.Length == 1 {
    i := 0;
    j := 0;
  } else {
    var first := a[0];
    var k: int := 1;
    
    while k < a.Length
      invariant 1 <= k <= a.Length
      invariant forall m :: 0 <= m < k ==> a[m] == first
    {
      if a[k] != first {
        i := 0;
        j := k;
        return;
      }
      k := k + 1;
    }
    
    i := 0;
    j := 0;
  }
}
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
    return true;
  }
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == a[0]
  {
    if a[i] != a[0] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

