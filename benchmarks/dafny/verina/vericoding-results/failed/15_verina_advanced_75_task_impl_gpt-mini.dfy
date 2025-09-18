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
/* helper modified by LLM (iteration 5): SpecSubarraySum empty interval equals 0 */
lemma SubarrayEmptyZero(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  ensures SpecSubarraySum(a, i, i) == 0
{
  assert SpecSubarraySum(a, i, i) == 0;
}

/* helper modified by LLM (iteration 5): extending subarray by one element adds a[end] */
lemma SubarrayExtend(a: seq<int>, start: int, end: int)
  requires 0 <= start <= end < |a|
  ensures SpecSubarraySum(a, start, end + 1) == SpecSubarraySum(a, start, end) + a[end]
  decreases end - start
{
  if start == end {
    assert SpecSubarraySum(a, start, start) == 0;
    assert SpecSubarraySum(a, start, start + 1) == a[start];
    assert SpecSubarraySum(a, start, start + 1) == SpecSubarraySum(a, start, start) + a[start];
  } else {
    SubarrayExtend(a, start + 1, end);
    assert SpecSubarraySum(a, start + 1, end + 1) == SpecSubarraySum(a, start + 1, end) + a[end];
    assert SpecSubarraySum(a, start, end + 1) == a[start] + SpecSubarraySum(a, start + 1, end + 1);
    assert SpecSubarraySum(a, start, end) == a[start] + SpecSubarraySum(a, start + 1, end);
    assert SpecSubarraySum(a, start, end + 1) == SpecSubarraySum(a, start, end) + a[end];
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
{
  /* code modified by LLM (iteration 5): brute-force max subarray with explicit assertions to prove existence */
  var n := sequence.Length;
  var a := sequence[..];
  var best := SpecSubarraySum(a, 0, 1);
  var bs := 0;
  var be := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bs < be <= n
    invariant SpecSubarraySum(a, bs, be) == best
    invariant forall s, e :: 0 <= s < e <= n && s < i ==> SpecSubarraySum(a, s, e) <= best
  {
    var sum := 0;
    var j := i;
    SubarrayEmptyZero(a, i);
    assert sum == SpecSubarraySum(a, i, j);
    while j < n
      invariant i <= j <= n
      invariant sum == SpecSubarraySum(a, i, j)
      invariant forall s, e :: 0 <= s < e <= n && (s < i || (s == i && e <= j)) ==> SpecSubarraySum(a, s, e) <= best
      invariant 0 <= bs < be <= n
      invariant SpecSubarraySum(a, bs, be) == best
    {
      sum := sum + a[j];
      SubarrayExtend(a, i, j);
      assert sum == SpecSubarraySum(a, i, j + 1);
      j := j + 1;
      if sum > best {
        best := sum;
        bs := i;
        be := j;
      }
    }
    i := i + 1;
  }
  result := best;
  assert 0 <= bs < be <= n;
  assert result == SpecSubarraySum(a, bs, be);
  assert forall s, e :: 0 <= s < e <= n ==> SpecSubarraySum(a, s, e) <= result;
}

// </vc-code>
