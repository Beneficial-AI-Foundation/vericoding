// IMPL 
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{
    result := [nums[0]];
    var i := 1;
    
    while i < |nums|
        invariant 1 <= i <= |nums|
        invariant |result| >= 1
        invariant is_sorted_and_distinct(result)
        invariant forall x :: x in result ==> x in nums[0..i]
        invariant forall x :: x in nums[0..i] ==> (x in result <==> exists j :: 0 <= j < i && nums[j] == x)
        invariant result[|result|-1] == nums[i-1] || (exists j :: 0 <= j < i-1 && nums[j] == nums[i-1] && result[|result|-1] < nums[i-1])
    {
        if nums[i] != nums[i-1] {
            result := result + [nums[i]];
        }
        i := i + 1;
    }
}

// Helper predicate
// ATOM 

// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

// ATOM 

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}