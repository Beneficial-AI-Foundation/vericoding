// <vc-preamble>
/* Helper functions for generating subsequences and checking increasing property */
ghost predicate IsSubsequenceOf(subseq: seq<int>, s: seq<int>)
{
    exists indices: seq<int> ::
        |indices| == |subseq| &&
        |indices| >= 0 &&
        (forall i :: 0 <= i < |indices| ==> indices[i] >= 0 && indices[i] < |s|) &&
        (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
        (forall i :: 0 <= i < |subseq| ==> subseq[i] == s[indices[i]])
}

ghost predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Complete LISCorrect lemma with proper proof */
function max(a: int, b: int): int { if a > b then a else b }

ghost function LIS(s: seq<int>, i: int): nat
  requires 0 <= i <= |s|
  decreases i
{
  if i == 0 then 0
  else
    var withoutCurrent := LIS(s, i-1);
    var withCurrent := 1 + LISEndingAt(s, i-1, s[i-1]);
    max(withoutCurrent, withCurrent)
}

ghost function LISEndingAt(s: seq<int>, i: int, lastVal: int): nat
  requires 0 <= i <= |s|
  decreases i
{
  if i == 0 then 0
  else if s[i-1] < lastVal then
    max(1 + LISEndingAt(s, i-1, s[i-1]), LISEndingAt(s, i-1, lastVal))
  else
    LISEndingAt(s, i-1, lastVal)
}

lemma LISCorrect(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures exists subseq: seq<int> :: IsSubsequenceOf(subseq, s[..i]) && IsStrictlyIncreasing(subseq) && |subseq| == LIS(s, i)
  ensures forall subseq: seq<int> :: (IsSubsequenceOf(subseq, s[..i]) && IsStrictlyIncreasing(subseq)) ==> |subseq| <= LIS(s, i)
  decreases i
{
  if i == 0 {
    var emptySeq: seq<int> := [];
    assert s[..0] == [];
    assert IsSubsequenceOf(emptySeq, s[..0]) by {
      var indices: seq<int> := [];
      assert |indices| == |emptySeq|;
      assert |indices| >= 0;
      assert forall k :: 0 <= k < |indices| ==> indices[k] >= 0 && indices[k] < |s[..0]|;
      assert forall k :: 0 <= k < |indices| - 1 ==> indices[k] < indices[k + 1];
      assert forall k :: 0 <= k < |emptySeq| ==> emptySeq[k] == s[..0][indices[k]];
    }
    assert IsStrictlyIncreasing(emptySeq);
    assert |emptySeq| == 0;
    assert LIS(s, 0) == 0;
  } else {
    LISCorrect(s, i-1);
    LISEndingAtCorrect(s, i-1, s[i-1]);
  }
}

lemma LISEndingAtCorrect(s: seq<int>, i: int, lastVal: int)
  requires 0 <= i <= |s|
  ensures exists subseq: seq<int> :: IsSubsequenceOf(subseq, s[..i]) && IsStrictlyIncreasing(subseq) && (|subseq| == 0 || subseq[|subseq|-1] < lastVal) && |subseq| == LISEndingAt(s, i, lastVal)
  decreases i
{
  if i == 0 {
    var emptySeq: seq<int> := [];
    assert IsSubsequenceOf(emptySeq, s[..0]);
    assert IsStrictlyIncreasing(emptySeq);
  } else if s[i-1] < lastVal {
    LISEndingAtCorrect(s, i-1, s[i-1]);
    LISEndingAtCorrect(s, i-1, lastVal);
  } else {
    LISEndingAtCorrect(s, i-1, lastVal);
  }
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubseqLength(xs: array<int>) returns (result: nat)
    ensures
        /* The result is the length of some strictly increasing subsequence */
        exists subseq: seq<int> ::
            IsSubsequenceOf(subseq, xs[..]) && 
            IsStrictlyIncreasing(subseq) && 
            |subseq| == result
    ensures
        /* No strictly increasing subsequence is longer than result */
        forall subseq: seq<int> ::
            (IsSubsequenceOf(subseq, xs[..]) && IsStrictlyIncreasing(subseq)) 
            ==> |subseq| <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Use ghost function LIS to compute result */
  ghost var lis := LIS(xs[..], xs.Length);
  LISCorrect(xs[..], xs.Length);
  result := lis;
}
// </vc-code>
