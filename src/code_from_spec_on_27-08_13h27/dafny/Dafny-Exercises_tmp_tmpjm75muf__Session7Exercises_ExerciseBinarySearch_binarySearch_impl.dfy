predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

// <vc-helpers>
lemma BinarySearchHelper(v: array<int>, elem: int, left: int, right: int, p: int)
  requires sorted(v[0..v.Length])
  requires 0 <= left <= right <= v.Length
  requires forall u :: 0 <= u < left ==> v[u] <= elem
  requires forall w :: right <= w < v.Length ==> v[w] > elem
  ensures -1 <= p < v.Length
  ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
{
  if left == 0 {
    assert p == -1;
    assert forall u :: 0 <= u <= p ==> false ==> v[u] <= elem; // vacuously true
    assert forall w :: p < w < v.Length ==> -1 < w < v.Length ==> 0 <= w < v.Length ==> v[w] > elem;
  } else {
    assert p == left - 1;
    assert 0 <= p < v.Length;
    assert forall u :: 0 <= u < left ==> v[u] <= elem;
    assert forall u :: 0 <= u <= p ==> 0 <= u < left ==> v[u] <= elem;
    assert forall w :: right <= w < v.Length ==> v[w] > elem;
    assert forall w :: p < w < v.Length ==> left <= w < v.Length ==> v[w] >= v[left-1];
    if left < v.Length {
      assert v[left-1] <= elem;
    }
    assert forall w :: p < w < v.Length ==> left <= w < v.Length ==> v[w] > elem;
  }
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
method BinarySearchImpl(v: array<int>, elem: int) returns (p: int)
  requires sorted(v[0..v.Length])
  ensures -1 <= p < v.Length
  ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
{
  var left := 0;
  var right := v.Length;
  
  while left < right
    invariant 0 <= left <= right <= v.Length
    invariant forall u :: 0 <= u < left ==> v[u] <= elem
    invariant forall w :: right <= w < v.Length ==> v[w] > elem
  {
    var mid := (left + right) / 2;
    if v[mid] <= elem {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  if left == 0 {
    p := -1;
  } else {
    p := left - 1;
  }
  BinarySearchHelper(v, elem, left, right, p);
}
// </vc-code>

//Recursive binary search