predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SortedExtend(a: array<int>, start: int, end: int, newEnd: int)
  requires 0 <= start <= end < newEnd <= a.Length
  requires sorted(a, start, end)
  requires forall k :: start <= k < end ==> a[k] <= a[end]
  ensures sorted(a, start, newEnd)
{
}

lemma SortedShift(a: array<int>, start: int, end: int, pos: int, oldVal: int)
  requires 0 <= start <= pos < end <= a.Length
  requires sorted(a, start, end)
  requires oldVal <= a[start] || (pos > start && a[pos-1] <= oldVal)
  ensures sorted(a, start, end)
{
}

lemma SortedCombine(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid < end <= a.Length
  requires sorted(a, start, mid+1)
  requires sorted(a, mid+1, end)
  requires mid < a.Length - 1
  requires a[mid] <= a[mid+1]
  ensures sorted(a, start, end)
{
}

lemma SortedInsert(a: array<int>, start: int, end: int, pos: int, val: int)
  requires 0 <= start <= pos <= end <= a.Length
  requires sorted(a, start, pos)
  requires sorted(a, pos+1, end+1)
  requires pos > start ==> a[pos-1] <= val
  requires pos < end ==> val <= a[pos+1]
  ensures sorted(a, start, end+1)
{
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
  {
    var key := a[i];
    var j := i - 1;
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant sorted(a, 0, j+1)
      invariant sorted(a, j+2, i+1)
      invariant forall k :: j+2 <= k <= i ==> key < a[k]
      invariant j >= 0 ==> a[j] > key
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j+1]
      modifies a
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    assert sorted(a, 0, j+1);
    assert sorted(a, j+1, i+1);
    assert sorted(a, 0, i+1);
    
    i := i + 1;
  }
}
// </vc-code>

