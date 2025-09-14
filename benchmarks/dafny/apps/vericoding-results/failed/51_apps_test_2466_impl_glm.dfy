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
function RemoveIndex(s: seq<int>, i: int): seq<int>
    requires 0 <= i < |s|
    ensures |RemoveIndex(s, i)| == |s| - 1
{
    s[0:i] + s[i+1..]
}

function AddToFront(e: int, perms: seq<seq<int>>): seq<seq<int>>
    ensures |AddToFront(e, perms)| == |perms|
    ensures forall p :: p in AddToFront(e, perms) ==> p[0] == e && p[1:] in perms
{
    if |perms| == 0 then [] else [e + [perms[0][0]]] + AddToFront(e, perms[1:])
}

lemma RemoveIndexAndRestoreMultiset(nums: seq<int>, i: int)
    requires 0 <= i < |nums| && AllDistinct(nums)
    ensures multiset([nums[i]] + RemoveIndex(nums, i)) == multiset(nums)
{
    calc {
        multiset([nums[i]] + RemoveIndex(nums, i));
        multiset([nums[i]]) + multiset(RemoveIndex(nums, i));
        multiset([nums[i]]) + (multiset(nums) - multiset([nums[i]]));
        multiset(nums);
    }
}

lemma ConcatenatePermutation(e: int, rest: seq<int>, p: seq<int>)
    requires AllDistinct([e] + rest)
    requires IsPermutation(p, rest)
    ensures IsPermutation([e] + p, [e] + rest)
{
    calc {
        |[e] + p|;
        1 + |p|;
        1 + |rest|;
        |[e] + rest|;
    }
    calc {
        multiset([e] + p);
        multiset([e]) + multiset(p);
        multiset([e]) + multiset(rest);
        multiset([e] + rest);
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
        return [ [] ];
    }
    var res: seq<seq<int>> := [];
    for i := 0 to |nums|
        invariant forall j :: 0 <= j < i ==> 
            (forall p :: p in permute(RemoveIndex(nums, j)) ==> [nums[j]] + p in res)
    {
        var first := nums[i];
        var rest := RemoveIndex(nums, i);
        var permsOfRest := permute(rest);
        for k := 0 to |permsOfRest|
            invariant forall q :: q in permsOfRest[0..k] ==> [first] + q in res
        {
            var p := permsOfRest[k];
            res := res + [[first] + p];
        }
    }
    return res;
}
// </vc-code>

