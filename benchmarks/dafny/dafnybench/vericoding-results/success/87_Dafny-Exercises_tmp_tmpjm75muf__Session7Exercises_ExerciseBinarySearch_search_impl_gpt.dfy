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
// no helpers needed
// </vc-helpers>

// <vc-spec>
method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
// </vc-spec>
// <vc-code>
{
  var p := binarySearch(v, elem);
  if p < 0 {
    b := false;

    assert !(elem in v[0..v.Length]) by {
      if elem in v[0..v.Length] {
        var i:int :| 0 <= i < v.Length && v[i] == elem;
        assert 0 <= i < v.Length;
        assert p < 0;
        assert p < i && i < v.Length;
        assert v[i] > elem;
        assert v[i] == elem;
      }
    }
  } else {
    b := v[p] == elem;

    if b {
      assert 0 <= p < v.Length;
      assert elem in v[0..v.Length] by {
        assert 0 <= p < v.Length;
        assert v[0..v.Length][p] == elem;
      }
    }

    if elem in v[0..v.Length] {
      var i:int :| 0 <= i < v.Length && v[i] == elem;
      if i > p {
        assert p < i && i < v.Length;
        assert v[i] > elem;
        assert v[i] == elem;
        assert false;
      }
      assert i <= p;
      if i < p {
        assert 0 <= i < p < v.Length;
        assert v[i] <= v[p];
        assert 0 <= p;
        assert v[p] <= elem;
        assert v[p] == elem;
      } else {
        assert i == p;
        assert v[p] == elem;
      }
      assert b;
    }
  }
}
// </vc-code>

//Recursive binary search