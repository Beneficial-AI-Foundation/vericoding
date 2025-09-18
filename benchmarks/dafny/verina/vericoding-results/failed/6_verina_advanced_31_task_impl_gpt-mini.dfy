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
/* helper modified by LLM (iteration 5): Reconstruct sequence from prev indices */
ghost function ReconstructSeq(prev: seq<int>, xs: seq<int>, i: int): seq<int>
  requires 0 <= i < |prev|
  requires prev[i] == -1 || (0 <= prev[i] < i)
  ensures IsSubsequenceOf(result, xs)
  ensures IsStrictlyIncreasing(result)
  ensures result[|result|-1] == xs[i]
  ensures |result| == 1 + (if prev[i] == -1 then 0 else |ReconstructSeq(prev, xs, prev[i])|)
  decreases i
{
  if prev[i] == -1 then [xs[i]] else ReconstructSeq(prev, xs, prev[i]) + [xs[i]]
}

/* helper modified by LLM (iteration 5): Relate indices of subsequence to DP lengths */
lemma IndicesSubseqLengthLeDp(xs: seq<int>, dp: seq<int>, indices: seq<int>)
  requires |dp| == |xs|
  requires |indices| >= 1
  requires (forall t :: 0 <= t < |indices| ==> 0 <= indices[t] < |xs|)
  requires (forall t :: 0 <= t < |indices|-1 ==> indices[t] < indices[t+1])
  requires (forall t :: 0 <= t < |indices|-1 ==> xs[indices[t]] < xs[indices[t+1]])
  requires (forall k,j :: 0 <= j < k < |dp| && xs[j] < xs[k] ==> dp[k] >= dp[j] + 1)
  requires (forall k :: 0 <= k < |dp| ==> dp[k] >= 1)
  ensures |indices| <= dp[indices[|indices|-1]]
  decreases |indices|
{
  if |indices| == 1 {
    // base case: dp[last] >= 1 by requirement
  } else {
    var prefix := indices[..|indices|-1];
    IndicesSubseqLengthLeDp(xs, dp, prefix);
    var last := indices[|indices|-1];
    var prevIdx := indices[|indices|-2];
    assert |prefix| <= dp[prevIdx];
    assert dp[last] >= dp[prevIdx] + 1;
    assert |indices| == |prefix| + 1;
    assert |indices| <= dp[last];
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
  /* code modified by LLM (iteration 5): implemented LIS with DP and proof; fixed call semicolon */
  var n := xs.Length;
  if n == 0 {
    result := 0;
    return;
  }
  var dp := new int[n];
  var prev := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant (forall k :: 0 <= k < i ==> dp[k] >= 1 && (prev[k] == -1 || (0 <= prev[k] < k)))
    invariant (forall k :: 0 <= k < i ==> (prev[k] == -1 && dp[k] == 1) || (0 <= prev[k] < k && dp[k] == dp[prev[k]] + 1))
    invariant (forall k,j :: 0 <= j < k < i && xs[j] < xs[k] ==> dp[k] >= dp[j] + 1)
  {
    dp[i] := 1;
    prev[i] := -1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1
    {
      if xs[j] < xs[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
        prev[i] := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var best := 0;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant 0 <= best < n
    invariant (forall t :: 0 <= t < k ==> dp[best] >= dp[t])
  {
    if dp[k] > dp[best] {
      best := k;
    }
    k := k + 1;
  }
  result := dp[best];

  var subseq := ReconstructSeq(prev[..], xs[..], best);
  assert IsSubsequenceOf(subseq, xs[..]);
  assert IsStrictlyIncreasing(subseq);
  assert |subseq| == result;

  assert (forall k,j :: 0 <= j < k < n && xs[j] < xs[k] ==> dp[k] >= dp[j] + 1);
  assert (forall k :: 0 <= k < n ==> dp[k] >= 1);

  assert (forall subseq0: seq<int> :: ((IsSubsequenceOf(subseq0, xs[..]) && IsStrictlyIncreasing(subseq0)) ==> |subseq0| <= result)) by {
    var subseq0: seq<int>;
    if IsSubsequenceOf(subseq0, xs[..]) && IsStrictlyIncreasing(subseq0) {
      var indices :| |indices| == |subseq0| &&
        (forall t :: 0 <= t < |indices| ==> 0 <= indices[t] < n) &&
        (forall t :: 0 <= t < |indices|-1 ==> indices[t] < indices[t+1]) &&
        (forall t :: 0 <= t < |subseq0| ==> subseq0[t] == xs[indices[t]]);
      call IndicesSubseqLengthLeDp(xs[..], dp[..], indices);
      assert |subseq0| <= dp[indices[|indices|-1]];
      assert dp[indices[|indices|-1]] <= dp[best];
      assert dp[best] == result;
    }
  }
}

// </vc-code>
