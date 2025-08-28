predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SortedPrefix(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  requires sorted(a, start, end)
  ensures sorted(a, start, mid)
{
}

lemma SortedAfterInsert(a: array<int>, start: int, end: int, pos: int, val: int)
  requires 0 <= start <= pos < end <= a.Length
  requires sorted(a, start, pos)
  requires sorted(a, pos + 1, end)
  requires pos == start || a[pos - 1] <= val
  requires pos + 1 == end || val <= a[pos + 1]
  requires a[pos] == val
  ensures sorted(a, start, end)
{
}

lemma SortedShift(a: array<int>, start: int, end: int)
  requires 0 <= start < end <= a.Length
  requires forall k :: start <= k < end - 1 ==> a[k] == a[k + 1]
  requires sorted(a, start + 1, end)
  ensures sorted(a, start, end - 1)
{
}

lemma InsertionSortHelper(a: array<int>, start: int, pos: int, end: int, key: int)
  requires 0 <= start <= pos < end <= a.Length
  requires sorted(a, start, pos)
  requires sorted(a, pos + 1, end)
  requires a[pos] == key
  requires pos == start || a[pos - 1] <= key
  requires pos + 1 == end || key <= a[pos + 1]
  ensures sorted(a, start, end)
{
}

lemma SortedConcatenate(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  requires sorted(a, start, mid)
  requires sorted(a, mid, end)
  requires mid == start || mid == end || a[mid - 1] <= a[mid]
  ensures sorted(a, start, end)
{
}

lemma SortedAfterShift(a: array<int>, j: int, i: int)
  requires 0 <= j + 1 <= i + 1 <= a.Length
  requires sorted(a, 0, j + 1)
  requires j + 2 <= i + 1 ==> sorted(a, j + 2, i + 1)
  requires j >= 0 && j + 1 < a.Length ==> a[j] <= a[j + 1]
  requires j + 2 <= i + 1 && j + 2 < a.Length ==> a[j + 1] <= a[j + 2]
  ensures sorted(a, 0, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
// </vc-spec>
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
      invariant sorted(a, 0, j + 1)
      invariant j + 2 <= i + 1 ==> sorted(a, j + 2, i + 1)
      invariant forall k :: j + 2 <= k <= i ==> a[k] >= key
      invariant a[j + 1] == key || (forall k :: j + 2 <= k <= i ==> a[k] == old(a[k - 1]))
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    
    assert sorted(a, 0, i + 1);
    
    i := i + 1;
  }
}
// </vc-code>
