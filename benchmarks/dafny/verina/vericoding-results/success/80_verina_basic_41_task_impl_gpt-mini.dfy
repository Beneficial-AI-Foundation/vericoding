// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllSame(a: array<int>)
    reads a
  {
    forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
  }

  lemma AllSameImpliesA0Equal(a: array<int>)
    requires a.Length > 0
    requires AllSame(a)
    ensures forall i :: 0 <= i < a.Length ==> a[i] == a[0]
  {
  }

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var all := true;
  var diffIndex := 0;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant all ==> (forall j :: 0 <= j < i ==> a[j] == a[0])
    invariant !all ==> 0 <= diffIndex < i && a[diffIndex] != a[0]
  {
    if a[i] != a[0] {
      all := false;
      diffIndex := i;
    }
    i := i + 1;
  }
  result := all;
}

// </vc-code>
