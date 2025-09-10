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

lemma DistinctPermutationsDistinct(perms: seq<seq<int>>, elem: int, rest: seq<int>)
    requires AllDistinct(rest)
    requires elem !in rest
    requires AllDistinct(perms)
    requires forall p :: p in perms ==> IsPermutation(p, rest)
    ensures AllDistinct(seq(|perms|, i requires 0 <= i < |perms| => [elem] + perms[i]))
{
    var extended := seq(|perms|, i requires 0 <= i < |perms| => [elem] + perms[i]);
    forall i, j | 0 <= i < j < |extended|
        ensures extended[i] != extended[j]
    {
        assert extended[i] == [elem] + perms[i];
        assert extended[j] == [elem] + perms[j];
        if extended[i] == extended[j] {
            assert perms[i] == perms[j];
            assert false;
        }
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
            invariant forall p :: p in result ==> 
                exists k :: 0 <= k < i && p[0] == nums[k]
            invariant forall k, perm :: 0 <= k < i && IsPermutation(perm, nums) && perm[0] == nums[k] ==> 
                perm in result
        {
            var elem := nums[i];
            var rest := nums[..i] + nums[i+1..];
            
            assert AllDistinct(rest) by {
                assert forall j, k :: 0 <= j < k < |rest| ==> rest[j] != rest[k];
            }
            
            var subPerms := permute(rest);
            
            assert |subPerms| == factorial(|rest|);
            assert |rest| == |nums| - 1;
            
            var j := 0;
            while j < |subPerms|
                invariant 0 <= j <= |subPerms|
                invariant |result| == i * factorial(|nums| - 1) + j
                invariant forall p :: p in result ==> IsPermutation(p, nums)
                invariant AllDistinct(result)
                invariant forall p :: p in result[i * factorial(|nums| - 1)..] ==>
                    p[0] == elem && p[1..] in subPerms[..j]
            {
                var newPerm := [elem] + subPerms[j];
                assert IsPermutation(newPerm, nums) by {
                    assert multiset(newPerm) == multiset([elem]) + multiset(subPerms[j]);
                    assert multiset(subPerms[j]) == multiset(rest);
                    assert multiset(rest) == multiset(nums) - multiset{elem};
                }
                result := result + [newPerm];
                j := j + 1;
            }
            
            i := i + 1;
        }
        
        assert |result| == factorial(|nums|) by {
            assert |result| == |nums| * factorial(|nums| - 1);
            PermutationCount(nums);
        }
    }
}
// </vc-code>

