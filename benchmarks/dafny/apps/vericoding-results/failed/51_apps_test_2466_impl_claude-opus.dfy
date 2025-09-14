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

// <vc-helpers>
lemma FactorialPositive(n: nat)
    ensures factorial(n) > 0
{
    if n == 0 {
        assert factorial(0) == 1;
    } else {
        FactorialPositive(n - 1);
    }
}

lemma PermutationCount(s: seq<int>)
    requires AllDistinct(s)
    ensures |s| == 0 ==> factorial(|s|) == 1
    ensures |s| > 0 ==> factorial(|s|) == |s| * factorial(|s| - 1)
{
}

lemma RestIsDistinct(nums: seq<int>, i: int)
    requires AllDistinct(nums)
    requires 0 <= i < |nums|
    ensures AllDistinct(nums[..i] + nums[i+1..])
{
    var rest := nums[..i] + nums[i+1..];
    forall j, k | 0 <= j < k < |rest|
        ensures rest[j] != rest[k]
    {
        if j < i && k < i {
            assert rest[j] == nums[j] && rest[k] == nums[k];
        } else if j < i && k >= i {
            assert rest[j] == nums[j] && rest[k] == nums[k+1];
        } else {
            assert rest[j] == nums[j+1] && rest[k] == nums[k+1];
        }
    }
}

lemma ExtendedPermutation(elem: int, subPerm: seq<int>, rest: seq<int>, nums: seq<int>)
    requires IsPermutation(subPerm, rest)
    requires multiset(rest) + multiset{elem} == multiset(nums)
    ensures IsPermutation([elem] + subPerm, nums)
{
    assert multiset([elem] + subPerm) == multiset{elem} + multiset(subPerm);
    assert multiset(subPerm) == multiset(rest);
    assert multiset([elem] + subPerm) == multiset{elem} + multiset(rest);
    assert multiset([elem] + subPerm) == multiset(nums);
}

lemma ExtendAllPerms(elem: int, subPerms: seq<seq<int>>, rest: seq<int>, nums: seq<int>)
    requires forall sp :: sp in subPerms ==> IsPermutation(sp, rest)
    requires multiset(rest) + multiset{elem} == multiset(nums)
    ensures forall j :: 0 <= j < |subPerms| ==> IsPermutation([elem] + subPerms[j], nums)
{
    forall j | 0 <= j < |subPerms|
        ensures IsPermutation([elem] + subPerms[j], nums)
    {
        ExtendedPermutation(elem, subPerms[j], rest, nums);
    }
}

lemma RestMultiset(nums: seq<int>, i: int)
    requires 0 <= i < |nums|
    ensures multiset(nums[..i] + nums[i+1..]) + multiset{nums[i]} == multiset(nums)
{
    if i == 0 {
        assert nums[..0] == [];
        assert nums == [nums[0]] + nums[1..];
    } else if i == |nums| - 1 {
        assert nums[i+1..] == [];
        assert nums == nums[..|nums|-1] + [nums[|nums|-1]];
    } else {
        assert nums == nums[..i] + [nums[i]] + nums[i+1..];
    }
}
// </vc-helpers>

// <vc-spec>
method permute(nums: seq<int>) returns (result: seq<seq<int>>)
    requires AllDistinct(nums)
    ensures |result| == factorial(|nums|)
    ensures forall p :: p in result ==> IsPermutation(p, nums)
    ensures AllDistinct(result)
    ensures forall perm :: IsPermutation(perm, nums) ==> perm in result
// </vc-spec>
// <vc-code>
{
    if |nums| == 0 {
        result := [[]];
    } else {
        result := [];
        var i := 0;
        while i < |nums|
            invariant 0 <= i <= |nums|
            invariant |result| == i * factorial(|nums| - 1)
            invariant forall p :: p in result ==> IsPermutation(p, nums)
            invariant AllDistinct(result)
        {
            var elem := nums[i];
            var rest := nums[..i] + nums[i+1..];
            
            RestIsDistinct(nums, i);
            var subPerms := permute(rest);
            
            RestMultiset(nums, i);
            ExtendAllPerms(elem, subPerms, rest, nums);
            
            var j := 0;
            while j < |subPerms|
                invariant 0 <= j <= |subPerms|
                invariant |result| == i * factorial(|nums| - 1) + j
                invariant forall p :: p in result ==> IsPermutation(p, nums)
            {
                var newPerm := [elem] + subPerms[j];
                result := result + [newPerm];
                j := j + 1;
            }
            
            i := i + 1;
        }
        
        assert |result| == |nums| * factorial(|nums| - 1);
        PermutationCount(nums);
    }
}
// </vc-code>

