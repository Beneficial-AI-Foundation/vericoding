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
lemma sorted_subsequence_sorted(nums: seq<int>, result: seq<int>)
    requires is_sorted(nums)
    requires forall x :: x in result ==> x in nums
    requires is_sorted_and_distinct(result)
    ensures is_sorted(result)
{
}

lemma distinct_elements_preserved(nums: seq<int>, result: seq<int>)
    requires is_sorted(nums)
    requires forall i :: i in nums <==> i in result
    requires is_sorted_and_distinct(result)
    ensures forall x :: x in nums ==> x in result
{
}

lemma no_duplicates_in_distinct_sorted(s: seq<int>)
    requires is_sorted_and_distinct(s)
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
}

lemma membership_preservation(original: seq<int>, filtered: seq<int>)
    requires forall x :: x in filtered ==> x in original
    requires forall x :: x in original ==> exists i :: 0 <= i < |filtered| && filtered[i] == x
    ensures forall x :: x in original <==> x in filtered
{
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
    if |nums| == 1 {
        return nums;
    }
    
    result := [nums[0]];
    var i := 1;
    
    while i < |nums|
        invariant 1 <= i <= |nums|
        invariant |result| >= 1
        invariant is_sorted_and_distinct(result)
        invariant forall x :: x in result ==> x in nums
        invariant forall j :: 0 <= j < i ==> (nums[j] in result)
        invariant result[|result|-1] == nums[i-1] || (exists k :: 0 <= k < i-1 && result[|result|-1] == nums[k] && nums[k] < nums[i-1])
    {
        if nums[i] != nums[i-1] {
            result := result + [nums[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

