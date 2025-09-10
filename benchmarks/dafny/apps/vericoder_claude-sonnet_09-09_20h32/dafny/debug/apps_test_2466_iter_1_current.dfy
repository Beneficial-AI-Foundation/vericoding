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
    } else {
        FactorialPositive(n - 1);
    }
}

lemma FactorialRecursive(n: nat)
    requires n > 0
    ensures factorial(n) == n * factorial(n - 1)
{
}

lemma PermutationReflexive(s: seq<int>)
    ensures IsPermutation(s, s)
{
}

lemma PermutationTransitive(a: seq<int>, b: seq<int>, c: seq<int>)
    requires IsPermutation(a, b) && IsPermutation(b, c)
    ensures IsPermutation(a, c)
{
}

lemma AllDistinctSubseq(s: seq<int>, i: int)
    requires AllDistinct(s)
    requires 0 <= i < |s|
    ensures AllDistinct(s[..i] + s[i+1..])
{
}

lemma PermutationWithoutElement(perm: seq<int>, original: seq<int>, i: int)
    requires IsPermutation(perm, original)
    requires 0 <= i < |perm|
    ensures IsPermutation(perm[..i] + perm[i+1..], original[..IndexOf(original, perm[i])] + original[IndexOf(original, perm[i])+1..])
{
}

function IndexOf(s: seq<int>, x: int): int
    requires x in s
    ensures 0 <= IndexOf(s, x) < |s|
    ensures s[IndexOf(s, x)] == x
{
    if s[0] == x then 0 else 1 + IndexOf(s[1..], x)
}

lemma InsertPreservesPermutation(perm: seq<int>, original: seq<int>, x: int, i: int)
    requires IsPermutation(perm, original)
    requires 0 <= i <= |perm|
    requires x !in perm
    requires x !in original
    ensures IsPermutation(perm[..i] + [x] + perm[i..], original + [x])
{
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
        return;
    }
    
    result := [];
    
    for i := 0 to |nums|
        invariant 0 <= i <= |nums|
        invariant forall p :: p in result ==> IsPermutation(p, nums)
        invariant forall p :: p in result ==> |p| == |nums|
        invariant AllDistinct(result)
    {
        var first := nums[i];
        var rest := nums[..i] + nums[i+1..];
        
        AllDistinctSubseq(nums, i);
        var subperms := permute(rest);
        
        for j := 0 to |subperms|
            invariant 0 <= j <= |subperms|
            invariant forall p :: p in result ==> IsPermutation(p, nums)
            invariant forall p :: p in result ==> |p| == |nums|
            invariant AllDistinct(result)
        {
            var subperm := subperms[j];
            var newperm := [first] + subperm;
            result := result + [newperm];
        }
    }
}
// </vc-code>

