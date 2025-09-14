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
lemma SearchEquivalence(s: seq<int>, elem: int, p: int)
  requires sorted(s)
  requires -1 <= p < |s|
  requires forall u :: 0 <= u <= p ==> s[u] <= elem
  requires forall w :: p < w < |s| ==> s[w] > elem
  ensures (elem in s) <==> (p >= 0 && s[p] == elem)
{
  if elem in s {
    var i :| 0 <= i < |s| && s[i] == elem;
    assert i <= p; // from forall w... requirement
    assert s[i] <= s[p]; // from sorted(s)
  }
}
// </vc-helpers>

// <vc-spec>
method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  var p := binarySearch(v, elem);
  SearchEquivalence(v[0..v.Length], elem, p);
  b := (p >= 0 && v[p] == elem);
}
// </vc-code>
