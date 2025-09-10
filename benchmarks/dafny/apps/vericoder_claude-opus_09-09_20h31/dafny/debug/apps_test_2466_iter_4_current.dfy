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
            assert extended[i][0] == elem;
            assert extended[j][0] == elem;
            assert extended[i][1..] == perms[i];
            assert extended[j][1..] == perms[j];
            assert perms[i] == extended[i][1..] == extended[j][1..] == perms[j];
            assert false;
        }
    }
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

lemma MultisetSliceEquality(nums: seq<int>, i: int)
    requires 0 <= i < |nums|
    ensures multiset(nums) == multiset(nums[..i]) + multiset{nums[i]} + multiset(nums[i+1..])
{
    if i == 0 {
        assert nums[..0] == [];
        assert multiset(nums[..0]) == multiset{};
        assert nums == [nums[0]] + nums[1..];
    } else if i == |nums| - 1 {
        assert nums[i+1..] == [];
        assert multiset(nums[i+1..]) == multiset{};
        assert nums == nums[..|nums|-1] + [nums[|nums|-1]];
    } else {
        assert nums == nums[..i] + [nums[i]] + nums[i+1..];
    }
}

lemma MultisetEquality(elem: int, rest: seq<int>, nums: seq<int>, i: int)
    requires 0 <= i < |nums|
    requires elem == nums[i]
    requires rest == nums[..i] + nums[i+1..]
    ensures multiset(rest) == multiset(nums) - multiset{elem}
{
    MultisetSliceEquality(nums, i);
    assert multiset(nums) == multiset(nums[..i]) + multiset{nums[i]} + multiset(nums[i+1..]);
    assert multiset(rest) == multiset(nums[..i]) + multiset(nums[i+1..]);
    assert multiset{nums[i]} == multiset{elem};
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
            invariant forall p :: p in result ==> |p| > 0 && exists k :: 0 <= k < i && p[0] == nums[k]
            invariant forall k, perm :: 0 <= k < i && IsPermutation(perm, nums) && |perm| > 0 && perm[0] == nums[k] ==> perm in result
        {
            var elem := nums[i];
            var rest := nums[..i] + nums[i+1..];
            
            RestIsDistinct(nums, i);
            assert AllDistinct(rest);
            
            var subPerms := permute(rest);
            
            assert |subPerms| == factorial(|rest|);
            assert |rest| == |nums| - 1;
            assert forall sp :: sp in subPerms ==> IsPermutation(sp, rest);
            
            var prevSize := |result|;
            var j := 0;
            while j < |subPerms|
                invariant 0 <= j <= |subPerms|
                invariant |result| == prevSize + j
                invariant prevSize == i * factorial(|nums| - 1)
                invariant forall p :: p in result ==> IsPermutation(p, nums)
                invariant AllDistinct(result)
                invariant forall idx :: prevSize <= idx < |result| ==>
                    |result[idx]| > 0 && result[idx][0] == elem && 
                    |result[idx]| > 1 && result[idx][1..] == subPerms[idx - prevSize]
                invariant forall p :: p in result[..prevSize] ==> 
                    |p| > 0 && exists k :: 0 <= k < i && p[0] == nums[k]
                invariant forall k, perm :: 0 <= k < i && IsPermutation(perm, nums) && |perm| > 0 && perm[0] == nums[k] ==> perm in result[..prevSize]
            {
                var newPerm := [elem] + subPerms[j];
                
                MultisetEquality(elem, rest, nums, i);
                assert multiset(rest) == multiset(nums) - multiset{elem};
                assert IsPermutation(subPerms[j], rest);
                assert multiset(subPerms[j]) == multiset(rest);
                assert multiset(newPerm) == multiset([elem]) + multiset(subPerms[j]);
                assert multiset(newPerm) == multiset{elem} + multiset(rest);
                assert multiset(newPerm) == multiset(nums);
                assert IsPermutation(newPerm, nums);
                
                result := result + [newPerm];
                j := j + 1;
            }
            
            assert forall idx :: prevSize <= idx < |result| ==> result[idx][0] == elem;
            assert forall perm :: IsPermutation(perm, nums) && |perm| > 0 && perm[0] == elem ==> perm in result by {
                forall perm | IsPermutation(perm, nums) && |perm| > 0 && perm[0] == elem
                    ensures perm in result
                {
                    var tail := perm[1..];
                    assert multiset(perm) == multiset{elem} + multiset(tail);
                    assert multiset(perm) == multiset(nums);
                    MultisetEquality(elem, rest, nums, i);
                    assert multiset(tail) == multiset(rest);
                    assert IsPermutation(tail, rest);
                    assert tail in subPerms;
                    var idx := 0;
                    while idx < |subPerms| && subPerms[idx] != tail
                        invariant 0 <= idx <= |subPerms|
                    {
                        idx := idx + 1;
                    }
                    assert idx < |subPerms| && subPerms[idx] == tail;
                    assert result[prevSize + idx] == [elem] + tail == perm;
                }
            }
            
            i := i + 1;
        }
        
        assert |result| == factorial(|nums|) by {
            assert |result| == |nums| * factorial(|nums| - 1);
            PermutationCount(nums);
        }
        
        assert forall perm :: IsPermutation(perm, nums) ==> perm in result by {
            forall perm | IsPermutation(perm, nums)
                ensures perm in result
            {
                if |perm| > 0 {
                    assert |perm| == |nums|;
                    assert multiset(perm) == multiset(nums);
                    assert perm[0] in multiset(perm);
                    assert perm[0] in multiset(nums);
                    var k := 0;
                    while k < |nums| && perm[0] != nums[k]
                        invariant 0 <= k <= |nums|
                        invariant forall m :: 0 <= m < k ==> perm[0] != nums[m]
                    {
                        k := k + 1;
                    }
                    assert k < |nums|;
                    assert perm[0] == nums[k];
                    assert perm in result;
                }
            }
        }
    }
}
// </vc-code>

