predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma binarySearchRecHelper(v: array<int>, elem: int, c: int, f: int, mid: int)
  requires sorted(v[0..v.Length])
  requires 0 <= c <= f+1 <= v.Length
  requires forall k :: 0 <= k < c ==> v[k] <= elem
  requires forall k :: f < k < v.Length ==> v[k] > elem
  requires c <= f
  requires mid == c + (f - c) / 2
{
  // Helper lemma to prove properties about the midpoint
  assert 0 <= mid < v.Length;
  
  if v[mid] <= elem {
    // If midpoint is <= elem, then all elements from c to mid are also <= elem
    assert forall k :: 0 <= k <= mid ==> v[k] <= elem;
    assert sorted(v[0..v.Length]) ==> forall u, w :: 0 <= u <= mid < w < v.Length ==> v[u] <= v[w];
  } else {
    // If midpoint > elem, then all elements from mid to f are also > elem
    assert forall k :: mid <= k < v.Length ==> v[k] > elem;
  }
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
    assert forall u :: 0 <= u <= f ==> v[u] <= elem;
    assert forall w :: f < w < v.Length ==> v[w] > elem;
    return;
  }
  
  var mid := c + (f - c) / 2;
  binarySearchRecHelper(v, elem, c, f, mid);
  
  if v[mid] <= elem {
    var p1 := binarySearchRec(v, elem, mid + 1, f);
    p := p1;
  } else {
    var p1 := binarySearchRec(v, elem, c, mid - 1);
    p := p1;
  }
}
// </vc-code>

