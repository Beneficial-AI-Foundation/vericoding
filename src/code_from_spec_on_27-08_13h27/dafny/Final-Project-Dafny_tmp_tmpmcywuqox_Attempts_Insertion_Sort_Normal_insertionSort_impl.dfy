predicate sorted (a: array<int>)

    reads a
{
    sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)

    requires 0 <= i <= a.Length
    reads a
{
    forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma sortedInsert(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires sortedA(a, i)
  requires i > 0 ==> forall j :: 0 < j < i ==> a[j-1] <= a[j]
  ensures sortedA(a, i+1)
  decreases a.Length - i
{
  // No array modifications in a lemma, as it is ghost code.
  // This lemma is not directly used for array updates but to reason about sortedness.
  if i > 0 {
    assert sortedA(a, i);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method insertionSort (a: array<int>)

    modifies a
    ensures sorted(a)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sortedA(a, i)
  {
    if i > 0 {
      var k := i - 1;
      while k >= 0 && a[k] > a[k+1]
        invariant -1 <= k < i
        invariant forall j :: 0 < j <= k ==> a[j-1] <= a[j]
        invariant forall j :: k+2 < j < i+1 ==> a[j-1] <= a[j]
        invariant k >= -1
        decreases k
      {
        var temp := a[k];
        a[k] := a[k+1];
        a[k+1] := temp;
        k := k - 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
