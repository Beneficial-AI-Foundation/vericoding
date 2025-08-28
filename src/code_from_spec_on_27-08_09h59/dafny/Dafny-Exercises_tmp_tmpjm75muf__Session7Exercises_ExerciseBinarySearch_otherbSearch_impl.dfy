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
lemma SortedSubsequence(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  requires sorted(v[0..v.Length])
  ensures sorted(v[i..j])
{
}

lemma SortedImpliesOrdered(v: array<int>, i: int, j: int)
  requires 0 <= i < j < v.Length
  requires sorted(v[0..v.Length])
  ensures v[i] <= v[j]
{
}

lemma ElementInSortedArray(v: array<int>, elem: int, i: int)
  requires 0 <= i < v.Length
  requires sorted(v[0..v.Length])
  requires v[i] == elem
  ensures elem in v[0..v.Length]
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
  if v.Length == 0 {
    return false, 0;
  }
  
  var low := 0;
  var high := v.Length;
  
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant forall u :: 0 <= u < low ==> v[u] < elem
    invariant forall w :: high <= w < v.Length ==> v[w] > elem
    invariant sorted(v[0..v.Length])
    decreases high - low
  {
    var mid := (low + high) / 2;
    
    if v[mid] == elem {
      ElementInSortedArray(v, elem, mid);
      return true, mid;
    } else if v[mid] < elem {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  return false, low;
}
// </vc-code>
