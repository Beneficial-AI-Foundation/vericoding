// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
predicate IsMajority(nums: seq<int>, v: int) { CountOccurrences(nums, v) > |nums| / 2 }
lemma CountOccurrences_Bounds(nums: seq<int>, v: int)
  ensures CountOccurrences(nums, v) <= |nums|
{ }
lemma NotBothMajorities(nums: seq<int>, x: int, y: int)
  ensures IsMajority(nums, x) && IsMajority(nums, y) ==> x == y
{ }
lemma CountOccurrences_DisjointSum(nums: seq<int>, x: int, y: int)
  requires x != y
  ensures CountOccurrences(nums, x) + CountOccurrences(nums, y) <= |nums|
{ }
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
{
  var n := nums.Length;
  var candidate := nums[0];
  var cnt := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant cnt >= 0
  {
    var x := nums[i];
    if cnt == 0 {
      candidate := x;
      cnt := 1;
    } else if x == candidate {
      cnt := cnt + 1;
    } else {
      cnt := cnt - 1;
    }
    i := i + 1;
  }
  var occ := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= occ <= i
  {
    if nums[i] == candidate {
      occ := occ + 1;
    }
    i := i + 1;
  }
  result := candidate;
}
// </vc-code>
