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
  var lo := 0;
  var hi := v.Length;

  while lo < hi
    invariant 0 <= lo <= hi <= v.Length
    invariant forall u :: 0 <= u < lo ==> v[u] < elem
    invariant forall w :: hi <= w < v.Length ==> v[w] > elem
    decreases hi - lo
  {
    var m := lo + (hi - lo) / 2;
    assert lo <= m < hi;

    if v[m] == elem {
      b := true;
      p := m;
      assert 0 <= p < v.Length;
      assert elem in v[0..v.Length];
      return;
    } else if v[m] < elem {
      assert 0 <= m < v.Length;
      assert forall u :: 0 <= u < m ==> v[u] <= v[m];
      assert forall u :: 0 <= u < m ==> v[u] < elem;
      lo := m + 1;
    } else {
      assert 0 <= m < v.Length;
      assert forall w :: m <= w < v.Length ==> v[w] > elem {
        if w == m {
        } else {
          assert v[m] <= v[w];
        }
      }
      hi := m;
    }
  }

  b := false;
  p := lo;
  assert 0 <= p <= v.Length;
  assert forall k :: 0 <= k < v.Length ==> v[k] != elem {
    if k < p {
      assert v[k] < elem;
    } else {
      assert p <= k < v.Length;
      assert v[k] > elem;
    }
  }
  assert !(elem in v[0..v.Length]);
}
// </vc-code>

