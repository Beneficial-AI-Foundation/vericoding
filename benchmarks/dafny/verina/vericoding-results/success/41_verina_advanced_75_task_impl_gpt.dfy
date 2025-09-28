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
/* helper modified by LLM (iteration 3): simple max function for integers */
function Max(a: int, b: int): int {
  if a >= b then a else b
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
  /* code modified by LLM (iteration 3): Added explicit triggers to quantifier invariants to avoid warnings; brute-force maximum subarray sum */
  var n := sequence.Length;
  var xs := sequence[..];

  var e := 1;
  var bestS := 0;
  var bestE := 1;
  result := SpecSubarraySum(xs, 0, 1);

  while e < n
    invariant 1 <= e <= n
    invariant 0 <= bestS < bestE <= e
    invariant result == SpecSubarraySum(xs, bestS, bestE)
    invariant forall s:int, ee:int {:trigger SpecSubarraySum(xs, s, ee)} :: 0 <= s < ee <= e ==> SpecSubarraySum(xs, s, ee) <= result
    decreases n - e
  {
    var s := 0;
    while s < e + 1
      invariant 0 <= s <= e + 1
      invariant 0 <= bestS < bestE <= e + 1
      invariant result == SpecSubarraySum(xs, bestS, bestE)
      invariant forall s0:int, ee:int {:trigger SpecSubarraySum(xs, s0, ee)} :: 0 <= s0 < ee <= e ==> SpecSubarraySum(xs, s0, ee) <= result
      invariant forall s0:int {:trigger SpecSubarraySum(xs, s0, e + 1)} :: 0 <= s0 < s ==> SpecSubarraySum(xs, s0, e + 1) <= result
      decreases e + 1 - s
    {
      var sum := SpecSubarraySum(xs, s, e + 1);
      if sum > result {
        result := sum;
        bestS := s;
        bestE := e + 1;
      }
      s := s + 1;
    }
    e := e + 1;
  }
}
// </vc-code>
