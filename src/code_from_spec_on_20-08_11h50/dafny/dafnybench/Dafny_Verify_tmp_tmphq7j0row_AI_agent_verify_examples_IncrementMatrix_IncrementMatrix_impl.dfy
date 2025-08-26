// The postcondition ensures that every element `a[i,j]` in the final array equals the corresponding element in the original array plus 1.

// I'll use nested loops to iterate through all elements and increment each one:

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
    invariant forall ii, jj :: i <= ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
      invariant forall jj :: 0 <= jj < j ==> a[i,jj] == old(a[i,jj]) + 1
      invariant forall jj :: j <= jj < a.Length1 ==> a[i,jj] == old(a[i,jj])
      invariant forall ii, jj :: i < ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>