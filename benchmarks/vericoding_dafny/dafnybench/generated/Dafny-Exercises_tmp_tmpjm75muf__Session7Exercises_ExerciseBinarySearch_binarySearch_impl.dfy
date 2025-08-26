The problem is in the loop invariants. Currently, I have `invariant forall w :: right < w < v.Length ==> v[w] > elem`, but when the loop exits (when `left > right`), I need to ensure that all elements after `p` are greater than `elem`.

The key insight is that when the loop terminates, `right < left`, and I need to connect the invariant about elements after `right` to the postcondition about elements after `p`. Since `p < left` (from the invariant) and `right < left` (loop termination condition), I need to strengthen the invariants to properly establish the postcondition.

<DAFNY FILE>
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
  if v.Length == 0 {
    return -1;
  }
  
  var left := 0;
  var right := v.Length - 1;
  p := -1;
  
  while left <= right
    invariant 0 <= left <= v.Length
    invariant -1 <= right < v.Length
    invariant -1 <= p < v.Length
    invariant forall u :: 0 <= u <= p ==> v[u] <= elem
    invariant forall w :: right < w < v.Length ==> v[w] > elem
    invariant p < left
    invariant p <= right
  {
    var mid := left + (right - left) / 2;
    
    if v[mid] <= elem {
      p := mid;
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
}
// </vc-code>

//Recursive binary search