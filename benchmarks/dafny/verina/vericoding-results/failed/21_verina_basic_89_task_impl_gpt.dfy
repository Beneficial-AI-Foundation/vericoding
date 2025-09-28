// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: seq<int>, x: int): bool {
  exists i: int :: 0 <= i < |s| && s[i] == x
}

/* helper modified by LLM (iteration 5): provide explicit existential witness using j == i */
lemma ContainsAtIndex(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures Contains(s, s[i])
{
  assert s[i] == s[i];
  assert exists j: int :: j == i && 0 <= j < |s| && s[j] == s[i];
  assert exists j: int :: 0 <= j < |s| && s[j] == s[i];
}

/* helper modified by LLM (iteration 5): make the existential witness explicit for preservation under append */
lemma ContainsPreservedByAppend(s: seq<int>, x: int, y: int)
  ensures Contains(s, y) ==> Contains(s + [x], y)
{
  if Contains(s, y) {
    var w :| 0 <= w < |s| && s[w] == y;
    assert 0 <= w < |s| + 1;
    assert (s + [x])[w] == s[w];
    assert exists j: int :: 0 <= j < |s| + 1 && (s + [x])[j] == y;
    assert Contains(s + [x], y);
  }
}

/* helper modified by LLM (iteration 5): provide explicit witness for appended element */
lemma ContainsAppendRight(s: seq<int>, x: int)
  ensures Contains(s + [x], x)
{
  assert |s + [x]| == |s| + 1;
  assert 0 <= |s| < |s + [x]|;
  assert (s + [x])[|s|] == x;
  assert exists j: int :: 0 <= j < |s + [x]| && (s + [x])[j] == x;
}

/* helper modified by LLM (iteration 2): show an index cannot equal x if x is not contained */
lemma NotContainsIndex(s: seq<int>, x: int, k: int)
  requires 0 <= k < |s|
  requires !Contains(s, x)
  ensures s[k] != x
{
  if s[k] == x {
    ContainsAtIndex(s, k);
    assert Contains(s, x);
    assert false;
  }
}

/* helper modified by LLM (iteration 3): removed assert-by; made explicit case analysis to avoid parser issues */
lemma UniquePreservedByAppend(s: seq<int>, x: int)
  requires forall k: int, l: int :: 0 <= k < l < |s| ==> s[k] != s[l]
  requires !Contains(s, x)
  ensures forall k: int, l: int :: 0 <= k < l < |s| + 1 ==> (s + [x])[k] != (s + [x])[l]
{
  forall k: int, l: int | 0 <= k < l < |s| + 1
    ensures (s + [x])[k] != (s + [x])[l]
  {
    if l < |s| {
      assert (s + [x])[k] == s[k];
      assert (s + [x])[l] == s[l];
      assert s[k] != s[l];
      assert (s + [x])[k] != (s + [x])[l];
    } else {
      assert l == |s|;
      assert (s + [x])[l] == x;
      assert k < |s|;
      assert (s + [x])[k] == s[k];
      NotContainsIndex(s, x, k);
      assert s[k] != x;
      assert (s + [x])[k] != (s + [x])[l];
    }
  }
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
  /* code modified by LLM (iteration 5): construct unique set-sequence and prove postconditions on result explicitly */
  var res: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k: int, l: int :: 0 <= k < l < |res| ==> res[k] != res[l]
    invariant forall k: int :: 0 <= k < |res| ==> Contains(s, res[k])
    invariant forall j: int :: 0 <= j < i ==> Contains(res, s[j])
    decreases |s| - i
  {
    if !Contains(res, s[i]) {
      var oldRes := res;
      res := oldRes + [s[i]];

      // preserve uniqueness
      UniquePreservedByAppend(oldRes, s[i]);

      // all elements of res are in s
      forall t: int | 0 <= t < |res|
        ensures Contains(s, res[t])
      {
        if t < |oldRes| {
          assert res[t] == oldRes[t];
          assert Contains(s, oldRes[t]);
        } else {
          assert t == |oldRes|;
          assert res[t] == s[i];
          ContainsAtIndex(s, i);
        }
      }

      // previously covered s-elements remain covered in res
      forall j0: int | 0 <= j0 < i
        ensures Contains(res, s[j0])
      {
        assert Contains(oldRes, s[j0]);
        ContainsPreservedByAppend(oldRes, s[i], s[j0]);
      }

      // the new element is contained in res
      ContainsAppendRight(oldRes, s[i]);
      assert Contains(res, s[i]);
    } else {
      assert Contains(res, s[i]);
    }
    i := i + 1;
  }

  assert i == |s|;
  result := res;

  // Uniqueness of result
  forall iu: int, ju: int | 0 <= iu < ju < |result|
    ensures result[iu] != result[ju]
  {
    assert |result| == |res|;
    assert 0 <= iu < ju < |res|;
    assert res[iu] != res[ju];
    assert result[iu] == res[iu];
    assert result[ju] == res[ju];
    assert result[iu] != result[ju];
  }

  // Every element in result is in s
  forall k: int | 0 <= k < |result|
    ensures exists j: int :: 0 <= j < |s| && s[j] == result[k]
  {
    assert |result| == |res|;
    assert 0 <= k < |res|;
    assert Contains(s, res[k]);
    var w: int :| 0 <= w < |s| && s[w] == res[k];
    assert result[k] == res[k];
    assert s[w] == result[k];
    assert exists j: int :: 0 <= j < |s| && s[j] == result[k];
  }

  // Every element in s is in result
  forall js: int | 0 <= js < |s|
    ensures exists j: int :: 0 <= j < |result| && result[j] == s[js]
  {
    assert i == |s|;
    assert Contains(res, s[js]);
    var w: int :| 0 <= w < |res| && res[w] == s[js];
    assert |result| == |res|;
    assert 0 <= w < |result|;
    assert result[w] == res[w];
    assert result[w] == s[js];
    assert exists j: int :: 0 <= j < |result| && result[j] == s[js];
  }
}
// </vc-code>
