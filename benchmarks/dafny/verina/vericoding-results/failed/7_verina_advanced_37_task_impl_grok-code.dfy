// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures var numsSeq := nums[..];
            var n := |numsSeq|;
            CountOccurrences(numsSeq, result) > n / 2 &&
            forall x: int :: x == result || CountOccurrences(numsSeq, x) <= n / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop to count occurrences and assertion to verify the candidate is the majority element */
{
  var i := 1;
  var cand := nums[0];
  var cnt := 1;
  while i < nums.Length
    invariant 0 < i <= nums.Length
    invariant 0 <= cnt <= i
  {
    if nums[i] == cand
    {
      cnt := cnt + 1;
    }
    else
    {
      cnt := cnt - 1;
      if cnt == 0
      {
        cand := nums[i];
        cnt := 1;
      }
    }
    i := i + 1;
  }
  var n := nums.Length;
  var count := 0;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant 0 <= count <= j
  {
    if nums[j] == cand
    {
      count := count + 1;
    }
    j := j + 1;
  }
  assert count > n / 2;
  result := cand;
}
// </vc-code>
