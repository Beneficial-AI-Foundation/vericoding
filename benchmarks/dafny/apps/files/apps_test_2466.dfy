Given a list of distinct integers, generate all possible permutations of the elements.
Each permutation should be a list containing all elements from the input in a different order.

function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n - 1)
}

predicate IsPermutation(perm: seq<int>, original: seq<int>)
{
    |perm| == |original| && multiset(perm) == multiset(original)
}

predicate AllDistinct<T(==)>(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

method permute_nums(nums: seq<int>, cur_permute: seq<int>) returns (all_permutes: seq<seq<int>>)
    requires AllDistinct(nums)
    requires forall x :: x in cur_permute ==> x !in nums
    ensures forall p :: p in all_permutes ==> IsPermutation(p, cur_permute + nums)
    ensures AllDistinct(all_permutes)
    ensures |all_permutes| == factorial(|nums|)
    ensures forall perm :: IsPermutation(perm, cur_permute + nums) ==> perm in all_permutes
{
    if |nums| == 0 {
        all_permutes := [cur_permute];
        return;
    }

    all_permutes := [];
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall p :: p in all_permutes ==> IsPermutation(p, cur_permute + nums)
        invariant AllDistinct(all_permutes)
        invariant |all_permutes| == i * factorial(|nums| - 1)
        invariant forall k :: 0 <= k < i ==> 
            (forall perm :: IsPermutation(perm, cur_permute + nums) && |cur_permute| < |perm| && perm[|cur_permute|] == nums[k] ==> perm in all_permutes)
        invariant forall p1, p2 :: p1 in all_permutes && p2 in all_permutes && p1 != p2 ==> 
            (|cur_permute| < |p1| && |cur_permute| < |p2| ==> p1[|cur_permute|] != p2[|cur_permute|])
    {
        var num := nums[i];
        var remaining := nums[0..i] + nums[i+1..];
        var new_cur_permute := cur_permute + [num];

        assert AllDistinct(remaining);
        assert forall x :: x in new_cur_permute ==> x !in remaining;

        // Prove the multiset equality
        assert multiset(nums[0..i]) + multiset([nums[i]]) + multiset(nums[i+1..]) == multiset(nums);
        assert multiset(remaining) + multiset([num]) == multiset(nums);
        assert multiset(new_cur_permute + remaining) == multiset(cur_permute + [num] + remaining);
        assert multiset(cur_permute + [num] + remaining) == multiset(cur_permute + nums);

        var sub_permutes := permute_nums(remaining, new_cur_permute);

        assert forall p :: p in sub_permutes ==> IsPermutation(p, new_cur_permute + remaining);
        assert forall p :: p in sub_permutes ==> IsPermutation(p, cur_permute + nums);

        // Prove distinctness is maintained
        assert forall p1 :: p1 in all_permutes ==> |cur_permute| < |p1| && p1[|cur_permute|] != nums[i];
        assert forall p2 :: p2 in sub_permutes ==> |cur_permute| < |p2| && p2[|cur_permute|] == nums[i];
        assert forall p1, p2 :: p1 in all_permutes && p2 in sub_permutes ==> p1 != p2;

        all_permutes := all_permutes + sub_permutes;
        i := i + 1;
    }
}

method permute(nums: seq<int>) returns (result: seq<seq<int>>)
    requires AllDistinct(nums)
    ensures |result| == factorial(|nums|)
    ensures forall p :: p in result ==> IsPermutation(p, nums)
    ensures AllDistinct(result)
    ensures forall perm :: IsPermutation(perm, nums) ==> perm in result
{
    result := permute_nums(nums, []);
}
