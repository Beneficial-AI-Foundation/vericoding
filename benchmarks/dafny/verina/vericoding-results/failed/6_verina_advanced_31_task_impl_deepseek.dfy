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
function ComputeSubsequenceLengths(xs: array<int>, i: int): (lengths: array<nat>)
  requires 0 <= i <= xs.Length
  ensures |lengths| == xs.Length
  ensures forall j :: 0 <= j < xs.Length ==> 0 <= lengths[j] <= xs.Length
{
  var lengths_arr := new nat[xs.Length];
  if i > 0 {
    var pos := i - 1;
    var maxTailLength := 0;
    while pos >= 0
      decreases pos + 1
    {
      if xs[pos] < xs[i] && lengths_arr[pos] > maxTailLength {
        maxTailLength := lengths_arr[pos];
      }
      pos := pos - 1;
    }
    lengths_arr[i] := maxTailLength + 1;
  } else {
    lengths_arr[i] := 1;
  }
  lengths_arr
}

lemma LemmaLongestIncreasingSubsequence(xs: seq<int>, subseq: seq<int>)
  requires IsSubsequenceOf(subseq, xs) && IsStrictlyIncreasing(subseq)
  ensures |subseq| <= xs.Length
{
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
  var n := xs.Length;
  if n == 0 {
    result := 0;
    return;
  }
  
  var lengths : array<nat>;
  lengths := new nat[n];
  var maxLength := 0;
  
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |lengths| == n
    invariant forall j :: 0 <= j < i ==> 0 <= lengths[j] <= n
    invariant maxLength >= 0 && maxLength <= n
    invariant maxLength == 0 || exists j :: 0 <= j < i && lengths[j] == maxLength
    decreases n - i
  {
    var currentMax := 0;
    for j := 0 to i - 1
      invariant 0 <= j <= i
      invariant currentMax >= 0 && currentMax <= n
      invariant forall k :: 0 <= k < j ==> (xs[k] < xs[i] ==> lengths[k] <= currentMax)
      decreases i - j
    {
      if xs[j] < xs[i] && lengths[j] > currentMax {
        currentMax := lengths[j];
      }
    }
    lengths[i] := currentMax + 1;
    
    if lengths[i] > maxLength {
      maxLength := lengths[i];
    }
  }
  
  result := maxLength;
}
// </vc-code>
