// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed set comprehension syntax error */
function BoyerMooreCandidate(nums: seq<int>, start: nat, end: nat): int
  requires 0 <= start < end <= |nums|
  requires end - start > 0
  decreases end - start
{
  if end - start == 1 then
    nums[start]
  else
    var mid := start + (end - start) / 2;
    var left := BoyerMooreCandidate(nums, start, mid);
    var right := BoyerMooreCandidate(nums, mid, end);
    var leftCount := CountInRange(nums, start, end, left);
    var rightCount := CountInRange(nums, start, end, right);
    if leftCount > rightCount then left else right
}

function CountInRange(nums: seq<int>, start: nat, end: nat, value: int): nat
  requires 0 <= start <= end <= |nums|
{
  |set i | start <= i < end && nums[i] == value|
}

lemma CardinalityOfRange(start: nat, end: nat)
  requires start <= end
  ensures |set i: nat | start <= i < end| == end - start
{
  if start == end {
    assert (set i: nat | start <= i < end) == {};
  } else {
    var s := set i: nat | start <= i < end;
    var s' := set i: nat | start <= i < end - 1;
    assert s == s' + {end - 1};
    assert end - 1 !in s';
    assert |s| == |s'| + 1;
    CardinalityOfRange(start, end - 1);
  }
}

lemma CountInRangeCorrect(nums: seq<int>, start: nat, end: nat, value: int)
  requires 0 <= start <= end <= |nums|
  ensures CountInRange(nums, start, end, value) <= end - start
{
  var s := set i | start <= i < end && nums[i] == value;
  var all := set i: nat | start <= i < end;
  assert s <= all;
  CardinalityOfRange(start, end);
  assert |all| == end - start;
}

lemma MajorityExistsInHalf(nums: seq<int>, start: nat, end: nat, maj: int)
  requires 0 <= start < end <= |nums|
  requires CountInRange(nums, start, end, maj) > (end - start) / 2
  ensures var mid := start + (end - start) / 2;
          CountInRange(nums, start, mid, maj) > (mid - start) / 2 ||
          CountInRange(nums, mid, end, maj) > (end - mid) / 2
{
  var mid := start + (end - start) / 2;
  var leftCount := CountInRange(nums, start, mid, maj);
  var rightCount := CountInRange(nums, mid, end, maj);
  var s1 := set i | start <= i < mid && nums[i] == maj;
  var s2 := set i | mid <= i < end && nums[i] == maj;
  var s := set i | start <= i < end && nums[i] == maj;
  assert s == s1 + s2;
  assert s1 * s2 == {};
  assert |s| == |s1| + |s2|;
  assert leftCount + rightCount == CountInRange(nums, start, end, maj);
}

lemma CandidateIsMajority(nums: seq<int>, start: nat, end: nat)
  requires 0 <= start < end <= |nums|
  requires exists maj :: CountInRange(nums, start, end, maj) > (end - start) / 2
  ensures var candidate := BoyerMooreCandidate(nums, start, end);
          CountInRange(nums, start, end, candidate) > (end - start) / 2
  decreases end - start
{
  var maj :| CountInRange(nums, start, end, maj) > (end - start) / 2;
  if end - start == 1 {
    assert nums[start] == maj;
  } else {
    var mid := start + (end - start) / 2;
    MajorityExistsInHalf(nums, start, end, maj);
    if CountInRange(nums, start, mid, maj) > (mid - start) / 2 {
      CandidateIsMajority(nums, start, mid);
    } else {
      CandidateIsMajority(nums, mid, end);
    }
  }
}

lemma CountOccurrencesEqualsCountInRange(nums: seq<int>, value: int)
  requires |nums| > 0
  ensures CountOccurrences(nums, value) == CountInRange(nums, 0, |nums|, value)
{
  var s1 := set i | 0 <= i < |nums| && nums[i] == value;
  var s2 := set i | 0 <= i < |nums| && nums[i] == value;
  assert s1 == s2;
}
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
/* code modified by LLM (iteration 5): Simplified implementation with proper existential handling */
{
  var numsSeq := nums[..];
  var n := |numsSeq|;
  
  ghost var maj: int;
  var exists_maj := false;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant exists_maj ==> CountOccurrences(numsSeq, maj) > n / 2
  {
    if CountOccurrences(numsSeq, numsSeq[i]) > n / 2 {
      maj := numsSeq[i];
      exists_maj := true;
      break;
    }
    i := i + 1;
  }
  
  assert exists_maj;
  CountOccurrencesEqualsCountInRange(numsSeq, maj);
  assert CountInRange(numsSeq, 0, n, maj) > n / 2;
  
  CandidateIsMajority(numsSeq, 0, n);
  result := BoyerMooreCandidate(numsSeq, 0, n);
  
  assert CountInRange(numsSeq, 0, n, result) > n / 2;
  CountOccurrencesEqualsCountInRange(numsSeq, result);
  assert CountOccurrences(numsSeq, result) > n / 2;
  
  forall x: int | x != result
    ensures CountOccurrences(numsSeq, x) <= n / 2
  {
    if CountOccurrences(numsSeq, x) > n / 2 {
      CountOccurrencesEqualsCountInRange(numsSeq, x);
      CountOccurrencesEqualsCountInRange(numsSeq, result);
      CountInRangeCorrect(numsSeq, 0, n, x);
      CountInRangeCorrect(numsSeq, 0, n, result);
      var sx := set i | 0 <= i < n && numsSeq[i] == x;
      var sr := set i | 0 <= i < n && numsSeq[i] == result;
      assert sx * sr == {};
      assert false;
    }
  }
}
// </vc-code>
