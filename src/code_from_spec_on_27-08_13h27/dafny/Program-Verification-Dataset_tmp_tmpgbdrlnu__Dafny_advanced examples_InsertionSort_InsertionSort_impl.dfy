predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SortedPreservation(a: array<int>, start: int, end: int, i: int)
  requires 0 <= start <= i <= end <= a.Length
  requires sorted(a, start, i)
  requires sorted(a, i, end)
  requires i > start ==> a[i-1] <= a[i]
  ensures sorted(a, start, end)
{
  forall j, k | start <= j < k < end
  ensures a[j] <= a[k]
  {
    if j < i && k >= i {
      assert a[j] <= a[i-1];
      if i > start {
        assert a[i-1] <= a[i];
      }
      assert a[i] <= a[k];
    }
  }
}

lemma SortedShift(a: array<int>, start: int, end: int, i: int, key: int)
  requires 0 <= start <= i < end <= a.Length
  requires sorted(a, start, i)
  requires i > start ==> forall k :: i <= k < end ==> a[k] >= key
  requires i == start ==> true
  ensures sorted(a, start, i + 1)
{
  forall j, k | start <= j < k < i + 1
  ensures a[j] <= a[k]
  {
    if k < i {
      assert a[j] <= a[k];
    } else if k == i {
      if j < i {
        assert sorted(a, start, i);
        assert a[j] <= a[i-1];
        if i > start {
          assert a[i-1] <= a[i];
        }
      }
    }
  }
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
method InsertionSortImpl(a: array<int>)
  requires a.Length > 0
  ensures sorted(a, 0, a.Length)
  modifies a
{
  if a.Length <= 1 {
    return;
  }
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sorted(a, 0, i)
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant forall k :: j + 1 <= k < i ==> a[k] >= key
      invariant sorted(a, 0, j + 1)
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    if j + 1 > 0 {
      SortedShift(a, 0, a.Length, j + 1, key);
    }
    i := i + 1;
  }
}
// </vc-code>
