predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma array_sorted_implies_monotonic(v: array<int>)
  requires sorted(v[0..v.Length])
  ensures forall i,j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
{
  // Follows directly from the definition of sorted on v[0..v.Length].
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
    return c - 1;
  }
  var mid := (c + f) / 2;
  if v[mid] <= elem {
    // Prepare and prove preconditions for recursive call binarySearchRec(v, elem, mid+1, f)
    assert 0 <= mid + 1 <= f + 1 <= v.Length;
    // From precondition forall k::0<=k<c ==> v[k]<=elem and sortedness we get
    // forall k::0<=k<mid+1 ==> v[k] <= elem
    array_sorted_implies_monotonic(v);
    assert v[mid] <= elem;
    assert forall k :: 0 <= k < mid+1 ==> v[k] <= elem;
    var p := binarySearchRec(v, elem, mid + 1, f);
    return p;
  } else {
    // v[mid] > elem
    // Prepare and prove preconditions for recursive call binarySearchRec(v, elem, c, mid-1)
    assert 0 <= c <= mid <= f;
    assert 0 <= c <= (mid - 1) + 1 <= v.Length;
    // From precondition forall k::f<k<v.Length ==> v[k]>elem and sortedness we get
    // forall k::mid-1<k<v.Length ==> v[k] > elem
    array_sorted_implies_monotonic(v);
    assert v[mid] > elem;
    assert forall k :: mid <= k < v.Length ==> v[k] > elem;
    var p := binarySearchRec(v, elem, c, mid - 1);
    return p;
  }
}
// </vc-code>

