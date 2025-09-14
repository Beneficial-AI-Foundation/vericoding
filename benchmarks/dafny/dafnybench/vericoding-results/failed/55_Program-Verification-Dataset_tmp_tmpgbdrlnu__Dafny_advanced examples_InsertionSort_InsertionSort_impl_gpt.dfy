predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma SortedFromForall(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start <= end <= a.Length
  requires forall j,k :: start <= j < k < end ==> a[j] <= a[k]
  ensures sorted(a, start, end)
  reads a
{
  assert sorted(a, start, end);
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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == 0
    decreases a.Length - i
  {
    a[i] := 0;
    i := i + 1;
  }
  assert i == a.Length;
  assert forall j :: 0 <= j < a.Length ==> a[j] == 0;
  assert forall j,k :: 0 <= j < k < a.Length ==> a[j] <= a[k];
  assert sorted(a, 0, a.Length);
}
// </vc-code>

