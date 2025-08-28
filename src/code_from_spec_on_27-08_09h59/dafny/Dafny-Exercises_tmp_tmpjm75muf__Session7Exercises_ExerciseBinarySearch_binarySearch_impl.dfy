predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>
lemma SortedSliceProperty(v: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= v.Length
  requires sorted(v[0..v.Length])
  ensures sorted(v[i..j])
{
}

lemma SortedTransitive(v: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k < v.Length
  requires sorted(v[0..v.Length])
  ensures v[i] <= v[j] <= v[k]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var low := 0;
  var high := v.Length;
  
  while low < high
    invariant 0 <= low <= high <= v.Length
    invariant forall u :: 0 <= u < low ==> v[u] <= elem
    invariant forall w :: high <= w < v.Length ==> v[w] > elem
  {
    var mid := low + (high - low) / 2;
    
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