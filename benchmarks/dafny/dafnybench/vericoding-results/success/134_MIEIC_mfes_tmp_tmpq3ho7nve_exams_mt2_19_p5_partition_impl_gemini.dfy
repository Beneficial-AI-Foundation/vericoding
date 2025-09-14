// <vc-preamble>
type T = int
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
// </vc-spec>
// <vc-code>
{
  // Lomuto partition scheme with the last element as the pivot.
  var pivotValue := a[a.Length-1];
  // 'i' is the store index for the next element smaller than the pivot.
  var i := 0;

  var j := 0;
  while j < a.Length - 1
    invariant 0 <= i <= j <= a.Length - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant a[a.Length - 1] == pivotValue
    invariant forall k :: 0 <= k < i ==> a[k] < pivotValue
    invariant forall k :: i <= k < j ==> a[k] >= pivotValue
  {
    if a[j] < pivotValue {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
    }
    j := j + 1;
  }

  // Swap pivot into its final sorted position.
  a[i], a[a.Length-1] := a[a.Length-1], a[i];
  pivotPos := i;
}
// </vc-code>
