predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {           
   forall j,k:: start<=j<k<end ==> a[j]<=a[k]
 }

// <vc-helpers>
lemma lemma_SwapPreservesOrder(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  requires a[i] > a[j]
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: k != i && k != j ==> a[k] == old(a[k])
  ensures old(sorted(a, 0, i)) ==> sorted(a, 0, i+1)
{
}

lemma lemma_ExtendSorted(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires sorted(a, 0, i)
  requires forall k :: i <= k < a.Length ==> a[i] <= a[k]
  ensures sorted(a, 0, i+1)
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
    var j := i;
    while j > 0 && a[j-1] > a[j]
      invariant 0 <= j <= i
      invariant sorted(a, 0, j)
      invariant forall k :: j < k <= i ==> a[j] <= a[k]
      decreases j
    {
      var temp := a[j];
      a[j] := a[j-1];
      a[j-1] := temp;
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>

