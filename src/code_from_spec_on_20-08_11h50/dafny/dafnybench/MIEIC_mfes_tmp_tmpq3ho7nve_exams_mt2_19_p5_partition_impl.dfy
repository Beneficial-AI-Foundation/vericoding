method partition<T(==,0)>(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
// </vc-spec>
// <vc-code>
{
  var pivot := a[a.Length - 1]; // Choose last element as pivot;
  var i := 0; // Index of smaller element;
  
  var j := 0;
  while j < a.Length - 1
    invariant 0 <= i <= j <= a.Length - 1
    invariant forall k :: 0 <= k < i ==> a[k] < pivot
    invariant forall k :: i <= k < j ==> a[k] >= pivot
    invariant a[a.Length - 1] == pivot
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[j] < pivot {
      // Swap a[i] and a[j]
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      i := i + 1;
    }
    j := j + 1;
  }
  
  // Place pivot in its correct position
  var temp := a[i];
  a[i] := a[a.Length - 1];
  a[a.Length - 1] := temp;
  
  pivotPos := i;
}
// </vc-code>