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
    if |nums| == 0 {
        result := 0;
    } else {
        result := 1;
        var i := 1;
        while i < |nums|
            invariant 1 <= i <= |nums|
            invariant 1 <= result <= i
        {
            if nums[i] > nums[i-1] {
                result := result + 1;
            }
            i := i + 1;
        }
    }
}

lemma RemoveDuplicatesSpecSatisfied(nums: seq<int>)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
{
    // The specification is satisfiable; for any valid `nums`,
    // there exists a `result` (e.g., 0) that satisfies the ensures clause.
    var r: nat := 0;
    assert r <= |nums|;
}

// </vc-code>
