predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  var l := -1;
  var h := v.Length;
  while l + 1 < h
    invariant -1 <= l < h <= v.Length
    invariant forall i :: 0 <= i <= l ==> v[i] <= elem
    invariant forall i :: h <= i < v.Length ==> v[i] > elem
    decreases h - l
  {
    var m := l + (h - l) / 2;
    assert 0 <= m < v.Length;
    if v[m] <= elem {
      l := m;
    } else {
      h := m;
    }
  }
  p := l;
  return;
}
// </vc-code>

//Recursive binary search