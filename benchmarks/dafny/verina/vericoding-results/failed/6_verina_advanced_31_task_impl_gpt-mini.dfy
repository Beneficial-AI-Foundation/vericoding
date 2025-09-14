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
/* helper modified by LLM (iteration 5): max of two ints */
function Max(a: int, b: int): int { if a >= b then a else b }

/* helper modified by LLM (iteration 5): prev index must be -1 or less than index (trivial lemma requiring the property) */
lemma PrevBound(k: int, p: int)
  requires p == -1 || p < k
  ensures p < k || p == -1
{ }

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
  /* code modified by LLM (iteration 5): recursive exhaustive best-subsequence computation using function methods */
  var n := xs.Length;

  // nested function: best subsequence of suffix j with all elements > v
  function method BestForValue(j: int, v: int): seq<int>
    requires 0 <= j <= n
    decreases n - j
    ensures IsSubsequenceOf(result, xs[j..])
    ensures IsStrictlyIncreasing(result)
    ensures forall other: seq<int> ::
      (IsSubsequenceOf(other, xs[j..]) && IsStrictlyIncreasing(other) && (forall t :: 0 <= t < |other| ==> other[t] > v)) ==> |other| <= |result|
  {
    if j == n then [] else
      let skip := BestForValue(j + 1, v) in
      if xs[j] > v then
        let take := [xs[j]] + BestForValue(j + 1, xs[j]) in
        if |take| > |skip| then take else skip
      else skip
  }

  // nested function: best subsequence of suffix i (no lower bound)
  function method Best(i: int): seq<int>
    requires 0 <= i <= n
    decreases n - i
    ensures IsSubsequenceOf(result, xs[i..])
    ensures IsStrictlyIncreasing(result)
    ensures forall other: seq<int> :: (IsSubsequenceOf(other, xs[i..]) && IsStrictlyIncreasing(other)) ==> |other| <= |result|
  {
    if i == n then [] else
      let skip := Best(i + 1) in
      let take := [xs[i]] + BestForValue(i + 1, xs[i]) in
      if |take| > |skip| then take else skip
  }

  var subseq := Best(0);
  result := |subseq|;

  // postcondition witnesses: subseq is a strictly increasing subsequence of xs and is maximal
  assert IsSubsequenceOf(subseq, xs[..]);
  assert IsStrictlyIncreasing(subseq);
  assert forall subseq': seq<int> :: (IsSubsequenceOf(subseq', xs[..]) && IsStrictlyIncreasing(subseq')) ==> |subseq'| <= result;
}

// </vc-code>
