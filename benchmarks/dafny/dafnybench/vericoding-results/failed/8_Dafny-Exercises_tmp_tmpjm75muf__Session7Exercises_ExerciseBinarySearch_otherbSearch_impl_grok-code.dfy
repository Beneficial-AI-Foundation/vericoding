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
method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && (forall w::p<=w<v.Length ==> v[w]>elem)
//Implement and verify
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
    decreases high - low
    invariant 0 <= low <= high <= v.Length
    invariant forall i :: 0 <= i < low ==> v[i] < elem
    invariant forall i :: high <= i < v.Length ==> v[i] > elem
  {
    var mid := low + (high - low) / 2;
    if v[mid] < elem {
      low := mid + 1;
    } else if v[mid] > elem {
      high := mid;
    } else {
      b := true;
      p := mid;
      return;
    }
  }
  b := false;
  p := low;
}
// </vc-code>

