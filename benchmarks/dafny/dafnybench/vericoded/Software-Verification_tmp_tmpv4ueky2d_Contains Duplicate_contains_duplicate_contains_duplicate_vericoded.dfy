predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

// <vc-helpers>
lemma SetSizeProperty(nums: seq<int>, s: set<int>, k: nat)
    requires k <= |nums|
    requires s == set i | 0 <= i < k :: nums[i]
    ensures |s| <= k
    ensures |s| == k <==> (forall i, j :: 0 <= i < j < k ==> nums[i] != nums[j])
{
    if k == 0 {
        assert s == {};
        assert |s| == 0;
    } else {
        var s' := set i | 0 <= i < k-1 :: nums[i];
        SetSizeProperty(nums, s', k-1);
        assert s == s' + {nums[k-1]};
        
        if nums[k-1] in s' {
            assert |s| == |s'|;
            assert |s| < k;
            var j :| 0 <= j < k-1 && nums[j] == nums[k-1];
            assert nums[j] == nums[k-1] && j < k-1;
        } else {
            assert |s| == |s'| + 1;
            if |s'| == k-1 {
                assert |s| == k;
                assert forall i, j :: 0 <= i < j < k-1 ==> nums[i] != nums[j];
                forall i, j | 0 <= i < j < k
                    ensures nums[i] != nums[j]
                {
                    if j == k-1 {
                        assert nums[k-1] !in s';
                        var l :| 0 <= l < k-1 && i == l;
                        assert nums[i] == nums[l];
                        assert nums[l] in s';
                        assert nums[i] != nums[k-1];
                    } else {
                        assert nums[i] != nums[j] by {
                            assert 0 <= i < j < k-1;
                        }
                    }
                }
            }
        }
    }
}

lemma DistinctImpliesSetSize(nums: seq<int>)
    requires distinct(nums)
    ensures |set i | 0 <= i < |nums| :: nums[i]| == |nums|
{
    var s := set i | 0 <= i < |nums| :: nums[i];
    SetSizeProperty(nums, s, |nums|);
    
    forall i, j | 0 <= i < j < |nums|
        ensures nums[i] != nums[j]
    {
        assert distinct(nums);
    }
    
    assert |s| == |nums|;
}

lemma NotDistinctImpliesSetSizeLess(nums: seq<int>)
    requires !distinct(nums)
    requires |nums| > 0
    ensures |set i | 0 <= i < |nums| :: nums[i]| < |nums|
{
    assert exists i, j :: 0 <= i < j < |nums| && nums[i] == nums[j];
    var s := set k | 0 <= k < |nums| :: nums[k];
    SetSizeProperty(nums, s, |nums|);
    assert |s| <= |nums|;
    
    var i, j :| 0 <= i < j < |nums| && nums[i] == nums[j];
    assert !(forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]);
    assert |s| < |nums|;
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
    var seen := {};
    var i := 0;
    
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant seen == set j | 0 <= j < i :: nums[j]
        invariant forall j, k :: 0 <= j < k < i ==> nums[j] != nums[k]
    {
        if nums[i] in seen {
            // Found a duplicate - not distinct
            return false;
        }
        seen := seen + {nums[i]};
        i := i + 1;
    }
    
    // No duplicates found - sequence is distinct
    assert i == |nums|;
    assert forall j, k :: 0 <= j < k < |nums| ==> nums[j] != nums[k];
    assert distinct(nums);
    
    return true;
}
// </vc-code>

