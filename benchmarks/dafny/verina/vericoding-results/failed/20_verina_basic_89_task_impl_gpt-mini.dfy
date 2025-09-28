// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate checks if value occurs in sequence */
function Contains(s: seq<int>, v: int): bool {
  exists i :: 0 <= i < |s| && s[i] == v
}

/* helper modified by LLM (iteration 5): lemma: after appending x to s, the new sequence contains x at last index */
lemma AppendContains(s: seq<int>, x: int)
  ensures Contains(s + [x], x)
{
  assert 0 <= |s|;
  assert (s + [x])[|s|] == x;
}

// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct sequence of unique elements from s preserving order and ensure postconditions */
  var res: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |res| ==> (exists j :: 0 <= j < i && s[j] == res[k])
    invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |res| && res[k] == s[j]
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    var x := s[i];
    var k := 0;
    var found := false;
    while k < |res|
      invariant 0 <= k <= |res|
      invariant found ==> (exists t :: 0 <= t < |res| && res[t] == x)
      invariant !found ==> forall t :: 0 <= t < k ==> res[t] != x
    {
      if res[k] == x {
        found := true;
      }
      k := k + 1;
    }
    if !found {
      var oldLen := |res|;
      res := res + [x];
      assert forall k2 :: 0 <= k2 < oldLen ==> (exists j :: 0 <= j < i && s[j] == res[k2]);
      assert res[oldLen] == x;
      assert exists j :: 0 <= j < i+1 && s[j] == res[oldLen];
      assert forall k3 :: 0 <= k3 < |res| ==> exists j :: 0 <= j < i+1 && s[j] == res[k3];
    } else {
      assert forall k4 :: 0 <= k4 < |res| ==> (exists j :: 0 <= j < i && s[j] == res[k4]);
      assert forall k4 :: 0 <= k4 < |res| ==> (exists j :: 0 <= j < i+1 && s[j] == res[k4]);
    }
    i := i + 1;
  }
  // loop exit implies i == |s|
  assert i == |s|;
  assert forall k :: 0 <= k < |res| ==> (exists j :: 0 <= j < |s| && s[j] == res[k]);
  assert forall j :: 0 <= j < |s| ==> (exists k :: 0 <= k < |res| && res[k] == s[j]);
  assert forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q];
  result := res;
}

// </vc-code>
