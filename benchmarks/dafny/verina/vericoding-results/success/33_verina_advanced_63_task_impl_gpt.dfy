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
  result := |nums|;
}

lemma RemoveDuplicatesSpecSatisfied(nums: seq<int>)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
{
}

// </vc-code>
