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
/* helper modified by LLM (iteration 5): Fixed syntax error in ValidMemo predicate with proper parentheses and brackets */
ghost function Max(a: nat, b: nat): nat
{
    if a > b then a else b
}

ghost predicate IsLongestIncreasingSubseq(subseq: seq<int>, xs: seq<int>)
{
    IsSubsequenceOf(subseq, xs) &&
    IsStrictlyIncreasing(subseq) &&
    (forall other: seq<int> ::
        (IsSubsequenceOf(other, xs) && IsStrictlyIncreasing(other)) ==> |other| <= |subseq|)
}

ghost function MemoLookup(memo: seq<nat>, i: int): nat
    requires 0 <= i < |memo|
{
    memo[i]
}

ghost predicate ValidMemo(memo: seq<nat>, xs: seq<int>)
{
    |memo| == |xs| &&
    (forall i :: 0 <= i < |xs| ==> memo[i] >= 1) &&
    (forall i :: 0 <= i < |xs| ==> 
        memo[i] == 1 + (max j | 0 <= j < i && xs[j] < xs[i] :: (if 0 <= j < |memo| then memo[j] else 0)))
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
  /* code modified by LLM (iteration 5): Maintained implementation with corrected helper syntax */
  var n := xs.Length;
  if n == 0 {
    result := 0;
    return;
  }
  
  var memo : array<nat>;
  memo := new nat[n];
  var maxLength := 1;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> memo[k] >= 1
    invariant maxLength >= 1
    invariant exists subseq: seq<int> :: IsSubsequenceOf(subseq, xs[..]) && IsStrictlyIncreasing(subseq) && |subseq| == maxLength
    invariant forall k :: 0 <= k < i ==> 
      memo[k] == 1 + (max j | 0 <= j < k && xs[j] < xs[k] :: (if 0 <= j < i then memo[j] else 0))
  {
    memo[i] := 1;
    var j := 0;
    var currentMax := 0;
    
    while j < i
      invariant 0 <= j <= i
      invariant memo[i] >= 1
      invariant currentMax == (max k | 0 <= k < j && xs[k] < xs[i] :: memo[k])
    {
      if xs[j] < xs[i] && memo[j] > currentMax {
        currentMax := memo[j];
      }
      j := j + 1;
    }
    
    memo[i] := 1 + currentMax;
    
    if memo[i] > maxLength {
      maxLength := memo[i];
    }
    
    i := i + 1;
  }
  
  result := maxLength;
}
// </vc-code>
