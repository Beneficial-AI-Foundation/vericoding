// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): verified standard binary search for lower bound */
  var low := 0;
  var high := v.Length;

  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant forall i :: 0 <= i < low ==> v[i] < elem
    invariant forall i :: high <= i < v.Length ==> v[i] >= elem
    invariant sorted(v[0..v.Length])
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if v[mid] < elem {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  p := low; // p is the insertion point

  if p < v.Length && v[p] == elem {
    b := true;
  } else {
    b := false;
  }
}
// </vc-code>
