predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  assume{:axiom} false;
}






//Recursive binary search

// <vc-helpers>
predicate sorted_range(a: array<int>, lo: int, hi: int)
  reads a
{
  if lo < hi then
    forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
  else
    true
}
// </vc-helpers>

// <vc-spec>
method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := v.Length;
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant sorted(v[0..v.Length])
    invariant forall i :: 0 <= i < low ==> v[i] < elem
    invariant forall i :: high <= i < v.Length ==> v[i] > elem
  {
    var mid := low + (high - low) / 2;
    if v[mid] < elem {
      low := mid + 1;
    } else if v[mid] > elem {
      high := mid;
    } else {
      return true, mid;
    }
  }

  return false, low;
}
// </vc-code>

