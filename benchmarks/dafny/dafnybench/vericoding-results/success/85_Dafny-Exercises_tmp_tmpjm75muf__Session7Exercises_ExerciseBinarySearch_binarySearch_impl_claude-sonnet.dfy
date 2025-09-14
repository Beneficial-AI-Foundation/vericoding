predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>
lemma sortedSliceProperty(v: array<int>, low: int, high: int, mid: int)
  requires 0 <= low <= mid < high <= v.Length
  requires sorted(v[0..v.Length])
  ensures sorted(v[low..high])
  ensures forall i :: low <= i < mid ==> v[i] <= v[mid]
  ensures forall i :: mid < i < high ==> v[mid] <= v[i]
{
}

lemma binarySearchInvariant(v: array<int>, elem: int, low: int, high: int)
  requires 0 <= low <= high <= v.Length
  requires sorted(v[0..v.Length])
  requires forall u :: 0 <= u < low ==> v[u] <= elem
  requires forall w :: high <= w < v.Length ==> v[w] > elem
  ensures forall u :: 0 <= u < low ==> v[u] <= elem
  ensures forall w :: high <= w < v.Length ==> v[w] > elem
{
}
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
    invariant forall u :: 0 <= u < low ==> v[u] <= elem
    invariant forall w :: high <= w < v.Length ==> v[w] > elem
    decreases high - low
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