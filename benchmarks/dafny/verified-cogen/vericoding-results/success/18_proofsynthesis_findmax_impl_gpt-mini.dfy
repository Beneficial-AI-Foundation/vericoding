// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MaxOfSeq(s: seq<int>): int
  requires |s| >= 1
  decreases |s|
{
  if |s| == 1 then s[0] else if MaxOfSeq(s[..|s|-1]) > s[|s|-1] then MaxOfSeq(s[..|s|-1]) else s[|s|-1]
}
// </vc-helpers>

// <vc-spec>
method FindMax(nums: array<int>) returns (ret: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> nums[i] <= ret
    ensures exists i :: 0 <= i < nums.Length && nums[i] == ret
// </vc-spec>
// <vc-code>
{
  var i := 1;
  ret := nums[0];
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> nums[j] <= ret
    invariant exists j :: 0 <= j < i && nums[j] == ret
  {
    if nums[i] > ret {
      ret := nums[i];
    }
    i := i + 1;
  }
}
// </vc-code>
