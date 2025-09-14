

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  var aSet: set<int> := {};
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant aSet == set k | 0 <= k < i :: a[k]
  {
    aSet := aSet + {a[i]};
    i := i + 1;
  }
  var bSet: set<int> := {};
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant bSet == set k | 0 <= k < j :: b[k]
  {
    bSet := bSet + {b[j]};
    j := j + 1;
  }
  result := (aSet * bSet) != {};
}
// </vc-code>

