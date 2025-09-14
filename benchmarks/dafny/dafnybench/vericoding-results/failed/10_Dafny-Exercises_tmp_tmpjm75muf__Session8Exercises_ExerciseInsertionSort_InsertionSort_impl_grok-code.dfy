predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
  if (a.Length == 0) {} 
  else {
    var i := 1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant sorted_seg(a,0,i-1)
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var key := a[i];
      var j := i-1;
      while j >= 0 && a[j] > key
        invariant -1 <= j <= i-1
        invariant sorted_seg(a,0,i-1)
        invariant forall k :: j+2 <= k <= i ==> a[k] >= key
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant sorted_seg(a,0,j) && (j < i-1 ==> sorted_seg(a,j+2,i-1))
      {
        a[j+1] := a[j];
        j := j-1;
      }
      a[j+1] := key;
      i := i+1;
    }
  }
}
// </vc-code>

