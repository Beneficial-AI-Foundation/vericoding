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

// <vc-helpers>
lemma binary_search_correctness(v: array<int>, elem: int, p: int)
  requires sorted(v[0..v.Length])
  requires -1 <= p < v.Length
  requires (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
  ensures (elem in v[0..v.Length]) <==> (p >= 0 && p < v.Length && v[p] == elem)
{
  if elem in v[0..v.Length] {
    var idx :| 0 <= idx < v.Length && v[idx] == elem;
    assert v[idx] <= elem;
    assert v[idx] > elem - 1;
    if p >= 0 && p < v.Length {
      if v[p] < elem {
        assert p < idx;
        assert v[p] <= elem;
      } else if v[p] > elem {
        assert idx <= p;
        assert v[idx] <= elem;
        assert elem < v[p];
        assert idx < p;
        assert v[idx] <= elem < v[p];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var p := binarySearch(v, elem);
  binary_search_correctness(v, elem, p);
  if p >= 0 && p < v.Length && v[p] == elem {
    b := true;
  } else {
    b := false;
  }
}
// </vc-code>

//Recursive binary search