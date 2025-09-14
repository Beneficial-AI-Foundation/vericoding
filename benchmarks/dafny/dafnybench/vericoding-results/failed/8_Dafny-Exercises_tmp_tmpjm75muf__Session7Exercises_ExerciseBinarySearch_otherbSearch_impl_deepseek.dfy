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






//Recursive binary search

// <vc-helpers>
lemma binarySearchLemma(v: array<int>, elem: int, low: int, high: int) 
  requires 0 <= low <= high + 1 <= v.Length
  requires sorted(v[0..v.Length])
  ensures 0 <= low <= v.Length
  ensures forall u :: 0 <= u < low ==> v[u] < elem
  ensures forall w :: low <= w < v.Length ==> v[w] >= elem
  decreases high - low
{
  if low <= high {
    var mid := low + (high - low) / 2;
    assert low <= mid <= high;
    if v[mid] < elem {
      assert forall u :: 0 <= u <= mid ==> v[u] <= v[mid] < elem;
      binarySearchLemma(v, elem, mid + 1, high);
    } else {
      binarySearchLemma(v, elem, low, mid - 1);
      assert v[mid] >= elem;
      assert forall w :: mid <= w < v.Length ==> v[w] >= v[mid] >= elem;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := v.Length - 1;
  
  while low <= high
    invariant 0 <= low <= high + 1 <= v.Length
    invariant forall u :: 0 <= u < low ==> v[u] < elem
    invariant forall w :: high < w < v.Length ==> v[w] > elem
  {
    var mid := low + (high - low) / 2;
    if v[mid] < elem {
      low := mid + 1;
    } else if v[mid] > elem {
      high := mid - 1;
    } else {
      b := true;
      p := mid;
      return;
    }
  }
  
  b := false;
  p := low;
  binarySearchLemma(v, elem, low, high);
  assert forall w :: low <= w < v.Length ==> v[w] >= elem;
  assert forall w :: high < w < v.Length ==> v[w] > elem;
  assert forall w :: p <= w < v.Length ==> v[w] > elem;
}
// </vc-code>

