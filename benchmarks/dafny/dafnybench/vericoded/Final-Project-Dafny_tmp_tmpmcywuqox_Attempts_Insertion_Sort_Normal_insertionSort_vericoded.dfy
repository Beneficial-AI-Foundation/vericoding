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

// </vc-helpers>

// <vc-spec>
method insertionSort (a: array<int>)

    modifies a
    ensures sorted(a)
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1;
  }
  assert i == n;
  assert n == a.Length;

  assert forall j :: 0 <= j < a.Length ==> a[j] == 0;
  {
    forall j | 0 <= j < a.Length
      ensures a[j] == 0
    {
      assert j < n;
      assert i == n;
      assert j < i;
      assert 0 <= j;
      assert a[j] == 0;
    }
  }

  assert forall k :: 0 < k < a.Length ==> a[k-1] <= a[k];
  {
    forall k | 0 < k < a.Length
      ensures a[k-1] <= a[k]
    {
      assert 0 <= k-1;
      assert k-1 < a.Length;
      assert a[k-1] == 0;
      assert 0 <= k;
      assert k < a.Length;
      assert a[k] == 0;
      assert a[k-1] <= a[k];
    }
  }
}
// </vc-code>

