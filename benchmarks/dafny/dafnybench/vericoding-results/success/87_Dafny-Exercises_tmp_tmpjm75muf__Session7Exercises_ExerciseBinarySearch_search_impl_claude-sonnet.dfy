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

// <vc-helpers>
lemma binary_search_correctness(v: array<int>, elem: int, p: int)
  requires sorted(v[0..v.Length])
  requires -1 <= p < v.Length
  requires (forall u :: 0 <= u <= p ==> v[u] <= elem) && (forall w :: p < w < v.Length ==> v[w] > elem)
  ensures (elem in v[0..v.Length]) <==> (p >= 0 && p < v.Length && v[p] == elem)
{
  if elem in v[0..v.Length] {
    var i :| 0 <= i < v.Length && v[i] == elem;
    if i <= p {
      assert v[i] <= elem;
      assert v[i] == elem;
    } else {
      assert v[i] > elem;
      assert v[i] == elem;
      assert false;
    }
    assert i <= p;
    assert v[i] <= elem && v[i] == elem;
    assert p >= 0;
    
    if p < v.Length {
      if v[p] < elem {
        assert v[p] <= elem && v[p] < elem;
        var j := p + 1;
        while j < v.Length && v[j] <= elem
          invariant p < j <= v.Length
          invariant forall k :: p < k < j ==> v[k] <= elem
        {
          j := j + 1;
        }
        if j < v.Length {
          assert v[j] > elem;
          assert p < j;
          assert false;
        }
      }
      assert v[p] >= elem;
      assert v[p] <= elem;
      assert v[p] == elem;
    }
  }
  
  if p >= 0 && p < v.Length && v[p] == elem {
    assert elem in v[0..v.Length];
  }
}
// </vc-helpers>

// <vc-spec>
method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
// </vc-spec>
// <vc-code>
{
  var pos := binarySearch(v, elem);
  binary_search_correctness(v, elem, pos);
  if pos >= 0 && pos < v.Length && v[pos] == elem {
    b := true;
  } else {
    b := false;
  }
}
// </vc-code>

//Recursive binary search