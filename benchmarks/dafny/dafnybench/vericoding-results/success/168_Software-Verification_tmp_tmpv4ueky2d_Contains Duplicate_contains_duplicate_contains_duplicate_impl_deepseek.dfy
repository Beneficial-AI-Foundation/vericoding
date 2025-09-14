predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

// <vc-helpers>
lemma lemma_distinct_property(nums: seq<int>, i: int, j: int)
    requires distinct(nums)
    requires 0 <= i < |nums| && 0 <= j < |nums|
    ensures i != j ==> nums[i] != nums[j]
{
}

lemma lemma_not_distinct_implies_duplicate(nums: seq<int>) 
    requires |nums| >= 1
    ensures !distinct(nums) ==> (exists i, j :: 0 <= i < j < |nums| && nums[i] == nums[j])
{
    if !distinct(nums) {
        var k :| 0 <= k < |nums| && !(forall l :: 0 <= l < |nums| && l != k ==> nums[k] != nums[l]);
        var m :| 0 <= m < |nums| && m != k && nums[k] == nums[m];
        assert 0 <= k < |nums| && 0 <= m < |nums| && k != m && nums[k] == nums[m];
    }
}
// </vc-helpers>

// <vc-spec>
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var i := 0;
    
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant distinct(nums[0..i])
        invariant forall x :: x in seen <==> (exists j :: 0 <= j < i && nums[j] == x)
    {
        if nums[i] in seen {
            result := false;
            assert exists j :: 0 <= j < i && nums[j] == nums[i];
            assert !distinct(nums);
            return;
        }
        seen := seen + {nums[i]};
        i := i + 1;
    }
    
    result := true;
}
// </vc-code>

