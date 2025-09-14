// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}

// <vc-helpers>
lemma sorted_implies_adjacent_duplicates(nums: seq<int>, i: int, j: int)
    requires is_sorted(nums)
    requires 0 <= i < j < |nums|
    requires nums[i] == nums[j]
    ensures forall k :: i <= k <= j ==> nums[k] == nums[i]
{
    if exists k :: i < k < j && nums[k] != nums[i] {
        var k :| i < k < j && nums[k] != nums[i];
        if nums[k] < nums[i] {
            assert nums[k] < nums[i] == nums[j];
            assert false;
        } else {
            assert nums[i] < nums[k];
            assert nums[k] <= nums[j];
            assert nums[i] == nums[j];
            assert false;
        }
    }
}

lemma sorted_distinct_append(s: seq<int>, x: int)
    requires is_sorted_and_distinct(s)
    requires |s| == 0 || s[|s|-1] < x
    ensures is_sorted_and_distinct(s + [x])
{
    var s' := s + [x];
    forall i, j | 0 <= i < j < |s'|
        ensures s'[i] < s'[j]
    {
        if j < |s| {
            assert s'[i] == s[i] && s'[j] == s[j];
        } else {
            assert j == |s| && s'[j] == x;
            if i < |s| {
                assert s'[i] == s[i];
                if |s| > 0 {
                    assert s[i] <= s[|s|-1];
                    assert s[|s|-1] < x;
                }
            }
        }
    }
}

lemma duplicate_exists_in_result(nums: seq<int>, result: seq<int>, i: int, last: int)
    requires is_sorted(nums)
    requires 0 < i < |nums|
    requires nums[i] <= last
    requires last in result
    requires forall x :: x in result ==> x in nums[..i]
    requires forall x :: x in nums[..i] ==> x in result || exists j :: 0 <= j < i && nums[j] == x && x in result
    ensures nums[i] in result || exists j :: 0 <= j <= i && nums[j] == nums[i] && nums[j] in result
{
    if nums[i] == last {
        assert last in result;
        assert nums[i] == last;
        assert nums[i] in result;
    } else {
        assert nums[i] < last;
        assert nums[i] in nums[..i];
        if nums[i] in result {
            // Done
        } else {
            assert exists j :: 0 <= j < i && nums[j] == nums[i] && nums[j] in result;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
// </vc-spec>
// <vc-code>
{
    if |nums| == 0 {
        return [];
    }
    
    result := [nums[0]];
    var last := nums[0];
    var i := 1;
    
    while i < |nums|
        invariant 1 <= i <= |nums|
        invariant |result| >= 1
        invariant is_sorted_and_distinct(result)
        invariant last == result[|result| - 1]
        invariant last in result
        invariant forall x :: x in result ==> x in nums[..i]
        invariant forall x :: x in nums[..i] ==> x in result || exists j :: 0 <= j < i && nums[j] == x && x in result
        invariant forall j :: 0 <= j < i && nums[j] > last ==> false
    {
        if nums[i] > last {
            sorted_distinct_append(result, nums[i]);
            result := result + [nums[i]];
            last := nums[i];
        } else {
            duplicate_exists_in_result(nums, result, i, last);
        }
        i := i + 1;
    }
}
// </vc-code>

