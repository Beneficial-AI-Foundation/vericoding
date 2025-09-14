predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted(a, 0, i)
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && key < a[j]
      invariant -1 <= j < i
      invariant sorted(a, 0, j+1)
      invariant sorted(a, j+1, i+1)
      invariant (forall k :: 0 <= k <= j ==> a[k] <= key)
      invariant (forall k :: j+1 <= k <= i ==> key <= a[k])
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    a[j+1] := key;
    i := i + 1;
  }
}
// </vc-code>

