// <vc-preamble>
function SubarraySum(numbers: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= numbers.Length
    reads numbers
    decreases end - start
{
    if start == end then 0
    else numbers[start] + SubarraySum(numbers, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): decomposition of SubarraySum when extending interval and adds decreases clause */
lemma SubarraySum_Extend(numbers: array<int>, start: int, end: int)
  requires 0 <= start <= end < numbers.Length
  ensures SubarraySum(numbers, start, end + 1) == SubarraySum(numbers, start, end) + numbers[end]
  decreases end - start
{
  if start == end {
    assert SubarraySum(numbers, start, start+1) == numbers[start];
    assert SubarraySum(numbers, start, start) == 0;
    assert SubarraySum(numbers, start, start+1) == SubarraySum(numbers, start, start) + numbers[end];
  } else {
    assert SubarraySum(numbers, start, end+1) == numbers[start] + SubarraySum(numbers, start+1, end+1);
    SubarraySum_Extend(numbers, start+1, end);
    assert SubarraySum(numbers, start+1, end+1) == SubarraySum(numbers, start+1, end) + numbers[end];
    assert numbers[start] + SubarraySum(numbers, start+1, end+1) == numbers[start] + (SubarraySum(numbers, start+1, end) + numbers[end]);
    assert numbers[start] + (SubarraySum(numbers, start+1, end) + numbers[end]) == (numbers[start] + SubarraySum(numbers, start+1, end)) + numbers[end];
    assert (numbers[start] + SubarraySum(numbers, start+1, end)) == SubarraySum(numbers, start, end);
    assert SubarraySum(numbers, start, end+1) == SubarraySum(numbers, start, end) + numbers[end];
  }
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySum(numbers: array<int>) returns (result: int)
    ensures result >= 0
    ensures forall start: int, end: int :: 
        start <= end && 0 <= start && end <= numbers.Length
        ==> SubarraySum(numbers, start, end) <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): brute-force enumeration of all subarrays with incremental sums */
  var n := numbers.Length;
  var best := 0;
  var end := 0;
  while end < n
    invariant 0 <= end <= n
    invariant best >= 0
    invariant forall s: int, e: int :: 0 <= s <= e <= end ==> SubarraySum(numbers, s, e) <= best
  {
    var newEnd := end + 1;
    var start := newEnd;
    var sum := 0;
    while start > 0
      invariant 0 <= start <= newEnd
      invariant sum == SubarraySum(numbers, start, newEnd)
      invariant forall s: int :: 0 <= s < newEnd && s >= start ==> SubarraySum(numbers, s, newEnd) <= best
      invariant forall s: int, e: int :: 0 <= s <= e <= end ==> SubarraySum(numbers, s, e) <= best
    {
      start := start - 1;
      sum := sum + numbers[start];
      SubarraySum_Extend(numbers, start, newEnd - 1);
      assert sum == SubarraySum(numbers, start, newEnd);
      if sum > best {
        best := sum;
      }
    }
    end := newEnd;
  }
  result := best;
}
// </vc-code>
