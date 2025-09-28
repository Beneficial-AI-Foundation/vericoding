// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): derive strict inequality from <= and != */
lemma LTFromLEAndNE(x: int, y: int)
  requires x <= y
  requires x != y
  ensures x < y
{}

/* helper modified by LLM (iteration 3): prove pairwise strictness from adjacent strictness (chain) */
lemma ChainLT(s: seq<int>, i: int, j: int)
  requires forall k :: 0 <= k < |s| - 1 ==> s[k] < s[k+1]
  requires 0 <= i < j < |s|
  ensures s[i] < s[j]
  decreases j - i
{
  if j == i + 1 {
    assert 0 <= i < |s| - 1;
    assert s[i] < s[i + 1];
  } else {
    ChainLT(s, i, j - 1);
    assert 0 <= j - 1 < |s| - 1;
    assert s[j - 1] < s[j];
    assert s[i] < s[j];
  }
}

/* helper modified by LLM (iteration 3): lift adjacent strictness to all index pairs */
lemma AdjacentImpliesAllPairs(s: seq<int>)
  requires forall k :: 0 <= k < |s| - 1 ==> s[k] < s[k+1]
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
  assert forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] by {
    forall i, j | 0 <= i < j < |s|
      ensures s[i] < s[j]
    {
      ChainLT(s, i, j);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)

    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): scan s, append at change points, maintain invariants, and prove strict order */
  var res: seq<int> := [];
  var i: int := 0;
  ghost var lastIdx: int := -1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant -1 <= lastIdx < i
    invariant (lastIdx == -1) <==> |res| == 0
    invariant lastIdx == -1 || res[|res|-1] == s[lastIdx]
    invariant forall k :: 0 <= k < |res| - 1 ==> res[k] < res[k+1]
    invariant forall t :: 0 <= t < |res| ==> exists j :: 0 <= j <= i && j < |s| && res[t] == s[j]
    invariant forall j :: 0 <= j < i ==> s[j] in res
    decreases |s| - i
  {
    if i == 0 || s[i] != s[i-1] {
      if |res| == 0 {
        res := res + [s[i]];
      } else {
        assert lastIdx >= 0;
        assert lastIdx < i;
        assert res[|res|-1] == s[lastIdx];
        if lastIdx == i - 1 {
          assert s[lastIdx] <= s[i-1];
        } else {
          assert lastIdx < i - 1;
          assert 0 <= lastIdx < i - 1;
          assert i > 0;
          assert i - 1 < |s|;
          assert s[lastIdx] <= s[i-1];
        }
        assert i > 0;
        assert s[i-1] <= s[i];
        assert s[i] != s[i-1];
        LTFromLEAndNE(s[i-1], s[i]);
        assert s[i-1] < s[i];
        assert s[lastIdx] <= s[i-1];
        assert s[lastIdx] < s[i];
        assert res[|res|-1] < s[i];
        res := res + [s[i]];
      }
      lastIdx := i;
      assert res[|res|-1] == s[lastIdx];
      assert s[i] in res;
    } else {
      assert i > 0;
      assert s[i] == s[i-1];
      assert s[i-1] in res;
      assert s[i] in res;
    }
    i := i + 1;
  }
  result := res;
  AdjacentImpliesAllPairs(result);
}
// </vc-code>
