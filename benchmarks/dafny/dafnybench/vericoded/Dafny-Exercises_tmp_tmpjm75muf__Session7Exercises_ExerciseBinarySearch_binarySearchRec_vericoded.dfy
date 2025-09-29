predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma SortedSubsequence(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  requires sorted(v[0..v.Length])
  ensures sorted(v[i..j])
{
  // This follows from the definition of sorted
}

lemma SortedTransitivity(v: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k < v.Length
  requires sorted(v[0..v.Length])
  ensures v[i] <= v[j] <= v[k]
{
  // This follows from the definition of sorted
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
    // Empty range - all elements before c are <= elem, so p = c-1
    p := c - 1;
  } else {
    var mid := c + (f - c) / 2;
    
    if v[mid] <= elem {
      // v[mid] <= elem, so all elements up to mid are <= elem
      // Continue searching in the upper half
      p := binarySearchRec(v, elem, mid + 1, f);
    } else {
      // v[mid] > elem, so all elements from mid onwards are > elem
      // Continue searching in the lower half
      p := binarySearchRec(v, elem, c, mid - 1);
    }
  }
}
// </vc-code>

