// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: seq<int>) returns (result: nat)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
    ensures result <= |nums|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant to properly track unique elements */
  if |nums| == 0 {
    result := 0;
  } else {
    var unique := 1;
    var i := 1;
    var lastUnique := nums[0];
    while i < |nums|
      invariant 1 <= i <= |nums|
      invariant 1 <= unique <= i
      invariant lastUnique == nums[0] || exists j :: 0 <= j < i && nums[j] == lastUnique
      invariant forall j :: 0 <= j < i && nums[j] != lastUnique ==> nums[j] < lastUnique
    {
      if nums[i] != lastUnique {
        unique := unique + 1;
        lastUnique := nums[i];
      }
      i := i + 1;
    }
    result := unique;
  }
}
// </vc-code>
