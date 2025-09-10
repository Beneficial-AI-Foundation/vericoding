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
function MultisetPlusOne<T>(m: multiset<T>, x: T): multiset<T> { m + multiset{x} }

lemma lemma_MultisetPlusOneCommutative<T>(m: multiset<T>, x: T, y: T)
    ensures MultisetPlusOne(MultisetPlusOne(m, x), y) == MultisetPlusOne(MultisetPlusOne(m, y), x)
{ }

lemma lemma_MultisetAddAssociative<T>(m1: multiset<T>, m2: multiset<T>, m3: multiset<T>)
    ensures (m1 + m2) + m3 == m1 + (m2 + m3)
{ }

lemma lemma_MultisetAddIdentity<T>(m: multiset<T>)
    ensures m + multiset{} == m
    ensures multiset{} + m == m
{ }

lemma lemma_MultisetCountExt<T(==)>(m: multiset<T>, x: T)
    ensures m[x] == (m + multiset{x})[x] - 1
{
    assert (m + multiset{x})[x] == m[x] + multiset{x}[x];
    assert multiset{x}[x] == 1;
}

lemma lemma_PermutationIsReflexive<T(==)>(s:seq<T>)
    ensures IsPermutation(s, s)
{
    assert multiset(s) == multiset(s);
}

lemma lemma_PermutationIsEmptyIf<T(==)>(s: seq<T>)
    requires |s| == 0
    ensures IsPermutation(s, [])
{
    assert s == [];
    assert multiset(s) == multiset([]);
}


predicate IsPermutationPrefix<T(==)>(perm: seq<T>, original: seq<T>)
{
    |perm| <= |original| && multiset(perm) <= multiset(original)
}

lemma lemma_IsPermutationPrefix_append<T(==)>(prefix: seq<T>, last: T, original: seq<T>)
    requires IsPermutationPrefix(prefix, original)
    requires last !in set prefix // Corrected: Use 'in' operator for sets instead of sequence slicing
    requires multiset{last} <= multiset(original) - multiset(prefix) // Corrected: Ensure the element count in original is sufficient
    ensures IsPermutationPrefix(prefix + [last], original)
{
    var m_pref = multiset(prefix);
    var m_orig = multiset(original);

    assert m_pref <= m_orig;
    assert (m_pref + multiset{last}) <= m_orig;
}

lemma lemma_IsPermutationPrefix_to_IsPermutation<T(==)>(prefix: seq<T>, original: seq<T>)
    requires IsPermutationPrefix(prefix, original)
    requires |prefix| == |original|
    ensures IsPermutation(prefix, original)
{
    assert multiset(prefix) == multiset(original);
}

lemma lemma_AllDistinctPrefix<T(==)>(s: seq<T>, k: nat)
    requires AllDistinct(s)
    requires k <= |s|
    ensures AllDistinct(s[0..k])
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
    if |nums| == 0 then
        return [[]];
    else if |nums| == 1 then
        return [nums];
    else
    {
        var result: seq<seq<int>> := [];
        var first := nums[0];
        var rest := nums[1..];

        var permsOfRest := permute(rest);

        forall p | p in permsOfRest
            ensures forall x :: x in (p + [first]) ==> x in nums
            ensures AllDistinct(p + [first])
            ensures IsPermutation(p + [first], nums)
        {
            var p_with_first := p + [first];
            assert p_with_first[|p_with_first|-1] == first;

            // Prove AllDistinct(p + [first])
            lemma_AllDistinctPrefix(nums, |rest|+1); // nums = [first] + rest
            assert AllDistinct(rest);
            assert first !in set rest;
            assert AllDistinct(p);
            assert first !in set p by {
                forall i | 0 <= i < |p|
                    ensures p[i] != first
                {
                    assert p[i] in set rest;
                    assert first !in set rest;
                }
            }
            assert AllDistinct(p + [first]);

            // Prove IsPermutation(p + [first], nums)
            assert IsPermutation(p, rest);
            assert multiset(p) == multiset(rest);
            assert multiset(p + [first]) == multiset(p) + multiset{first};
            assert multiset(p + [first]) == multiset(rest) + multiset{first};
            assert multiset(nums) == multiset{first} + multiset(rest) by {
                assert multiset(nums) == multiset([first]) + multiset(rest);
                assert multiset([first]) == multiset{first};
            }
            assert multiset(p + [first]) == multiset(nums);
            assert |p + [first]| == |p| + 1 == |rest| + 1 == |nums|;
            assert IsPermutation(p + [first], nums);

            var currentPerm: seq<int>;
            forall i | 0 <= i <= |p|
                invariant 0 <= i <= |p|
                invariant forall k :: 0 <= k < i ==> IsPermutation(result[k], nums)
                invariant forall k, l :: 0 <= k < l < i ==> result[k] != result[l]
            {
                var prefix := p[0..i];
                var suffix := p[i..];
                currentPerm := prefix + [first] + suffix;

                // Prove |currentPerm| == |nums|
                assert |currentPerm| == |prefix| + 1 + |suffix| == i + 1 + (|p| - i) == |p| + 1 == |nums|;

                // Prove AllDistinct(currentPerm)
                assert AllDistinct(p); // from permsOfRest
                assert first !in set p;

                lemma_AllDistinctPrefix(currentPerm, i + 1); // prefix + [first]
                assert AllDistinct(prefix + [first]);
                assert first !in set suffix;
                lemma_AllDistinctPrefix(currentPerm, |currentPerm|);
                assert AllDistinct(suffix);
                assert AllDistinct(prefix + [first] + suffix);

                // Prove IsPermutation(currentPerm, nums)
                assert multiset(currentPerm) == multiset(prefix) + multiset{first} + multiset(suffix);
                assert multiset(currentPerm) == multiset(prefix + suffix) + multiset{first} by {
                    lemma_MultisetAddAssociative(multiset(prefix), multiset{first}, multiset(suffix));
                    lemma_MultisetAddAssociative(multiset(prefix), multiset(suffix), multiset{first});
                }

                assert multiset(prefix + suffix) == multiset(p);
                assert multiset(currentPerm) == multiset(p) + multiset{first};
                assert multiset(p) == multiset(rest);
                assert multiset(currentPerm) == multiset(rest) + multiset{first};
                assert multiset(nums) == multiset(rest) + multiset{first};
                assert multiset(currentPerm) == multiset(nums);
                assert IsPermutation(currentPerm, nums);

                result := result + [currentPerm];
            }
        }
        return result;
    }
}
// </vc-code>

