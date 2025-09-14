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
  var low := 0;
  var high := v.Length;
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant forall i::0 <= i < low ==> v[i] <= elem
    invariant forall i::high <= i < v.Length ==> v[i] > elem
  {
    var mid := (low + high) / 2;
    if v[mid] <= elem {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  p := low - 1;
}
// </vc-code>

//Recursive binary search