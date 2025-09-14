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
    var seen := {};
    result := 0;
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant result <= i
        invariant result <= |nums|
    {
        if nums[i] !in seen {
            seen := seen + {nums[i]};
            result := result + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
