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
lemma SortedSubarray(v: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= v.Length
  requires sorted(v[0..v.Length])
  ensures sorted(v[lo..hi])
{
  // The proof follows from the definition of sorted
}

lemma SortedImpliesOrdered(v: array<int>, i: int, j: int)
  requires 0 <= i < j < v.Length
  requires sorted(v[0..v.Length])
  ensures v[i] <= v[j]
{
  // Direct from sorted definition
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
  var lo := 0;
  var hi := v.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= v.Length
    invariant forall k :: 0 <= k < lo ==> v[k] < elem
    invariant forall k :: hi <= k < v.Length ==> v[k] > elem
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    
    if v[mid] < elem {
      lo := mid + 1;
    } else if v[mid] > elem {
      hi := mid;
    } else {
      // Found the element
      b := true;
      p := mid;
      return;
    }
  }
  
  // Element not found
  b := false;
  p := lo;
}
// </vc-code>

