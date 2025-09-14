predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SortedSubset(a: array<int>, start: int, end: int, i: int, j: int)
  requires 0 <= start <= i < j < end <= a.Length
  requires sorted(a, start, end)
  ensures a[i] <= a[j]
{
  // This follows directly from the definition of sorted
}

lemma SortedTransitive(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  requires sorted(a, start, mid)
  requires sorted(a, mid, end)
  requires mid > start && mid < end ==> a[mid-1] <= a[mid]
  ensures sorted(a, start, end)
{
  // This proves that if two adjacent sorted regions share a proper boundary, the whole region is sorted
}
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
    decreases a.Length - i
  {
    var key := a[i];
    ghost var a_before := a[..];
    var j := i - 1;
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant forall k :: j+2 <= k <= i ==> a[k] == a_before[k-1]
      invariant forall k :: 0 <= k <= j ==> a[k] == a_before[k]
      invariant forall k :: i+1 <= k < a.Length ==> a[k] == a_before[k]
      invariant sorted(a, 0, j+1)
      invariant sorted(a, j+2, i+1)
      invariant forall k :: j+2 <= k <= i ==> a[k] > key
      invariant j >= 0 ==> a[j] > key
      decreases j
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    i := i + 1;
  }
}
// </vc-code>

