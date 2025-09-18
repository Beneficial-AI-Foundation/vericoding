// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that IsSubseqAt implies index bounds */
lemma IsSubseqAtImpliesBounds(sub: seq<int>, main: seq<int>, i: int)
  requires IsSubseqAt(sub, main, i)
  ensures 0 <= i && i + |sub| <= |main|
{
  // IsSubseqAt predicate includes these bounds in its definition
  assert 0 <= i && i + |sub| <= |main|;
}

/* helper modified by LLM (iteration 5): lemma that equality over range implies IsSubseqAt */
lemma CheckEqualityImpliesIsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
  requires 0 <= i && i + |sub| <= |main|
  requires (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
  ensures IsSubseqAt(sub, main, i)
{
  // The conjunction of the bounds and the equality across the range yields the predicate
  assert 0 <= i && i + |sub| <= |main|;
  assert (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j]);
  assert IsSubseqAt(sub, main, i);
}

// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterate through possible starts and prove existence when found */
  var n := |main|;
  var m := |sub|;
  if m > n {
    result := false;
    return;
  }
  var i := 0;
  while i <= n - m
    invariant 0 <= i <= n - m + 1
    invariant forall k :: 0 <= k < i ==> !(IsSubseqAt(sub, main, k))
    decreases n - m - i
  {
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant forall t :: 0 <= t < j ==> sub[t] == main[i + t]
      decreases m - j
    {
      if sub[j] != main[i + j] { break; }
      j := j + 1;
    }
    if j == m {
      // equality across the whole sub-sequence holds at position i and bounds hold
      CheckEqualityImpliesIsSubseqAt(sub, main, i);
      result := true;
      return;
    }
    // mismatch at position j (< m) proves that i is not a valid start
    assert 0 <= j < m;
    assert sub[j] != main[i + j];
    if IsSubseqAt(sub, main, i) {
      // From IsSubseqAt we'd get sub[j] == main[i + j], contradiction
      assert sub[j] == main[i + j];
      assert false;
    }
    i := i + 1;
  }
  result := false;
}

// </vc-code>
