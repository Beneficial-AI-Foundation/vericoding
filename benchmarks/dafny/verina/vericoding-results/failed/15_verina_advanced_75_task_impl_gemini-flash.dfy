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
/* helper modified by LLM (iteration 5): Corrected MaxEndingHere and MaxContiguousSubarraySum for proper inductive definition */
function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function MaxEndingHere(s: seq<int>, k: int) : int
    requires 0 <= k <= |s|
    decreases k
{
    if k == 0 then 0
    else Max(s[k-1], s[k-1] + Max(0, MaxEndingHere(s, k-1)))
}

function MaxContiguousSubarraySum(s: seq<int>, k: int): int
    requires 0 <= k <= |s|
    decreases k
{
    if k == 0 then -2147483648 // Smallest possible integer to represent no sum yet
    else Max(MaxContiguousSubarraySum(s, k-1), MaxEndingHere(s, k))
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
/* code modified by LLM (iteration 5): Corrected initialization and loop invariants for Kadane's algorithm. */
{
  var s_seq := sequence[..];

  var currentMax: int := s_seq[0]; // Represents MaxEndingHere(s_seq, i)
  var globalMax: int := s_seq[0]; // Represents MaxContiguousSubarraySum(s_seq, i) excluding the first element (index 0)

  for i := 1 to sequence.Length
    invariant 0 < i <= sequence.Length
    invariant currentMax == Max(s_seq[i-1], Max(0, MaxEndingHere(s_seq, i-1)) + s_seq[i-1]) // Correct definition of MaxEndingHere for current step
    invariant globalMax == MaxContiguousSubarraySum(s_seq, i)
  {
    currentMax := Max(s_seq[i-1], currentMax + s_seq[i-1]);
    globalMax := Max(globalMax, currentMax);
  }
  result := globalMax;
}
// </vc-code>
