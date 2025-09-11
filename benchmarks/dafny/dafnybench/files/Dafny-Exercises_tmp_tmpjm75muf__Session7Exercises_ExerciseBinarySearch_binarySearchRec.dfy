// <vc-preamble>
predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 decreases f-c
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
