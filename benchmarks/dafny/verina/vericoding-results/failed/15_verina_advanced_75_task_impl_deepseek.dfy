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

function ComputeMaxSubarraySum(seq: seq<int>, startIdx: int, endIdx: int): int
  requires 0 <= startIdx <= endIdx <= |seq|
  decreases endIdx - startIdx
{
  if startIdx == endIdx then
    0
  else
    max(
      SpecSubarraySum(seq, startIdx, endIdx),
      ComputeMaxSubarraySum(seq, startIdx + 1, endIdx),
      ComputeMaxSubarraySum(seq, startIdx, endIdx - 1)
    )
}

/* helper modified by LLM (iteration 4): Fixed lemma syntax error */
lemma MaxSubarrayExists(seq: seq<int>, n: int)
  requires n > 0
  requires |seq| >= n
  ensures exists s: int, e: int :: 0 <= s < e <= n && 
    SpecSubarraySum(seq, s, e) == ComputeMaxSubarraySum(seq, 0, n)
{
  if n == 1 {
    // Base case: single element array
  } else {
    MaxSubarrayExists(seq, n - 1);
  }
}

function max(a: int, b: int, c: int): int
{
  max(max(a, b), c)
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
{
  /* code modified by LLM (iteration 4): Fixed compilation errors */
  var n := sequence.Length;
  MaxSubarrayExists(sequence[..], n);
  result := ComputeMaxSubarraySum(sequence[..], 0, n);
}
// </vc-code>
