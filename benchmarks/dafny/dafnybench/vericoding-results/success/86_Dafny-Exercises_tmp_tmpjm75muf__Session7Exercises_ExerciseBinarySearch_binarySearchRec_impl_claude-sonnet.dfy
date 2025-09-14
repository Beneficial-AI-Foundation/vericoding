predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma sortedSliceProperty(v: array<int>, i: int, j: int, k: int)
  requires sorted(v[0..v.Length])
  requires 0 <= i <= k < j <= v.Length
  ensures v[i] <= v[k] <= v[j-1]
{
}

lemma sortedTransitivity(v: array<int>, i: int, j: int)
  requires sorted(v[0..v.Length])
  requires 0 <= i < j < v.Length
  ensures v[i] <= v[j]
{
}
// </vc-helpers>

// <vc-spec>
method binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 decreases f-c
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  if c > f {
    p := f;
    return;
  }
  
  var mid := (c + f) / 2;
  
  if v[mid] <= elem {
    p := binarySearchRec(v, elem, mid + 1, f);
  } else {
    p := binarySearchRec(v, elem, c, mid - 1);
  }
}
// </vc-code>

