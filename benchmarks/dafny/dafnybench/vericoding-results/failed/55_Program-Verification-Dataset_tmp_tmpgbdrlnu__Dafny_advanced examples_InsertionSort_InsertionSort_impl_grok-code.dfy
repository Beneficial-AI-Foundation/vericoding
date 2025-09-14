predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
// Insertion Sort helpers - no additional code needed for this implementation
// </vc-helpers>

// <vc-spec>
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
// </vc-spec>
// <vc-code>
{
  for i := 1 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant sorted(a, 0, i)
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a)[k]
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant sorted(a, 0, j+1)
      invariant forall k :: 0 <= k < j+1 ==> a[k] == old(a)[k]
      invariant forall k :: j+2 <= k <= i ==> a[k] == old(a)[k]
      decreases j
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
  }
}
// </vc-code>

