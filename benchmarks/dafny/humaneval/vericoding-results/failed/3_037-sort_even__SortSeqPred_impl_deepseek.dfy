// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add helper function to track multiset preservation during swaps */
function CountTrue(p: seq<bool>, start: int, end: int): int
  requires 0 <= start <= end <= |p|
  decreases end - start
{
  if start == end then 0
  else (if p[start] then 1 else 0) + CountTrue(p, start+1, end)
}

lemma CountTrueLemma(p: seq<bool>, start: int, end: int)
  requires 0 <= start <= end <= |p|
  ensures CountTrue(p, start, end) == CountTrue(p, start, end)
  decreases end - start
{
  if start < end {
    CountTrueLemma(p, start+1, end);
  }
}

lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s[0..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]) == multiset(s)
{
  assert multiset(s[0..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]) ==
         multiset(s[0..i]) + multiset([s[j]]) + multiset(s[i+1..j]) + multiset([s[i]]) + multiset(s[j+1..]);
  assert multiset(s) == multiset(s[0..i]) + multiset([s[i]]) + multiset(s[i+1..j]) + multiset([s[j]]) + multiset(s[j+1..]);
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplify with selection sort approach */
  var n := |s|;
  sorted := s;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == n
    invariant multiset(sorted) == multiset(s)
    invariant forall k :: 0 <= k < n && !p[k] ==> sorted[k] == s[k]
    invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
    decreases n - i
  {
    if p[i] {
      var min_idx := i;
      var j := i + 1;
      while j < n
        invariant i <= min_idx < n
        invariant i < j <= n
        invariant forall k :: i <= k < j && p[k] ==> sorted[min_idx] <= sorted[k]
        invariant |sorted| == n
        invariant multiset(sorted) == multiset(s)
        invariant forall k :: 0 <= k < n && !p[k] ==> sorted[k] == s[k]
        invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
        decreases n - j
      {
        if p[j] && sorted[j] < sorted[min_idx] {
          min_idx := j;
        }
        j := j + 1;
      }
      
      if min_idx != i {
        // Swap elements
        var temp := sorted[i];
        sorted := sorted[0..i] + [sorted[min_idx]] + sorted[i+1..min_idx] + [temp] + sorted[min_idx+1..];
        // Update the multiset invariant
        assert multiset(sorted) == multiset(s);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
