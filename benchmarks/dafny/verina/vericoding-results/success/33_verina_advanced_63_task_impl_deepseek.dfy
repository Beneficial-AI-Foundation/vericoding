// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: seq<int>) returns (result: nat)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
    ensures result <= |nums|
// </vc-spec>
// <vc-code>
{
  if |nums| == 0 {
    result := 0;
  } else {
    var i := 0;
    var j := 1;
    while j < |nums|
      invariant 0 <= i < j <= |nums|
      invariant i <= |nums|
      invariant forall k :: 0 <= k <= i ==> nums[k] == (if k == 0 then nums[0] else max(nums[0], nums[k]))
      invariant nums[i] <= nums[j-1]
      decreases |nums| - j
    {
      if nums[j] != nums[j-1] {
        i := i + 1;
      }
      j := j + 1;
    }
    result := i + 1;
  }
}
// </vc-code>
