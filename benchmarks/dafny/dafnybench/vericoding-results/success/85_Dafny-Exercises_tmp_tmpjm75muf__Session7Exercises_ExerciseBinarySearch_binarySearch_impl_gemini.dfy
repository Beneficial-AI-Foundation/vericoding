// <vc-preamble>
predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added requires clauses to prevent index out-of-range errors */
predicate LowInv(s: seq<int>, elem: int, low: int)
  requires 0 <= low <= |s|
{
  forall i :: 0 <= i < low ==> s[i] <= elem
}

/* helper modified by LLM (iteration 2): added requires clauses to prevent index out-of-range errors */
predicate HighInv(s: seq<int>, elem: int, high: int)
  requires 0 <= high <= |s|
{
  forall i :: high <= i < |s| ==> s[i] > elem
}
// </vc-helpers>

// <vc-spec>
method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): standard binary search implementation */
  var low := 0;
  var high := v.Length;
  var V := v[0..v.Length];
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant sorted(V)
    invariant LowInv(V, elem, low)
    invariant HighInv(V, elem, high)
  {
    var mid := low + (high - low) / 2;
    if mid < v.Length && v[mid] <= elem { // mid can be out of bounds if v.Length=0
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  p := low - 1;
}
// </vc-code>
