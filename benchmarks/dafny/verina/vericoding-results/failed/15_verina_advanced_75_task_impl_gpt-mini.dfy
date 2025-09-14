// <vc-preamble>
function SpecSubarraySum(sequence: seq<int>, start: int, end: int): int
    decreases end - start
{
    if start >= end || start < 0 || end > |sequence| then
        0
    else if start + 1 == end then
        sequence[start]
    else
        sequence[start] + SpecSubarraySum(sequence, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Unfold SpecSubarraySum for valid indices */
lemma SpecSubarraySumUnfold(seq: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |seq|
    ensures SpecSubarraySum(seq, start, end) == if start >= end then 0 else seq[start] + SpecSubarraySum(seq, start + 1, end)
    decreases end - start
{
  if start >= end {
    // both sides are 0 by function definition
  } else if start + 1 == end {
    // both sides are sequence[start] by function definition
  } else {
    // For the remaining case, the function definition gives the desired equality
    assert SpecSubarraySum(seq, start, end) == seq[start] + SpecSubarraySum(seq, start + 1, end);
  }
}
// </vc-helpers>

// <vc-spec>
method TaskCode(sequence: array<int>) returns (result: int)
    requires sequence.Length > 0
    ensures 
        exists start: int, end: int :: 
            0 <= start < end <= sequence.Length && 
            result == SpecSubarraySum(sequence[..], start, end) &&
            forall s: int, e: int :: (0 <= s < e <= sequence.Length) ==> 
                SpecSubarraySum(sequence[..], s, e) <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented maximum subarray via nested loops maintaining invariants */
{
  var n := sequence.Length;
  ghost var bestStart := 0;
  ghost var bestEnd := 1;
  result := sequence[0];
  var s := 0;
  while s < n
    invariant 0 <= s <= n
    invariant 0 <= bestStart < bestEnd <= n
    invariant result == SpecSubarraySum(sequence[..], bestStart, bestEnd)
    invariant forall a,b :: 0 <= a < b <= n && a < s ==> SpecSubarraySum(sequence[..], a, b) <= result
  {
    var e := s;
    var sum := 0;
    while e < n
      invariant s <= e <= n
      invariant sum == SpecSubarraySum(sequence[..], s, e)
      invariant 0 <= bestStart < bestEnd <= n
      invariant result == SpecSubarraySum(sequence[..], bestStart, bestEnd)
      invariant forall a,b :: 0 <= a < b <= n && (a < s || (a == s && b <= e)) ==> SpecSubarraySum(sequence[..], a, b) <= result
    {
      sum := sum + sequence[e];
      e := e + 1;
      if sum > result {
        result := sum;
        bestStart := s;
        bestEnd := e;
      }
    }
    s := s + 1;
  }
  assert 0 <= bestStart < bestEnd <= n;
  assert result == SpecSubarraySum(sequence[..], bestStart, bestEnd);
  assert forall a,b :: 0 <= a < b <= n ==> SpecSubarraySum(sequence[..], a, b) <= result;
}
// </vc-code>
