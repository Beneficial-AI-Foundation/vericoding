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
    ensures factorial(n) > 0 || n == 0
{
    if n > 0 {
        FactorialPositive(n - 1);
    }
}

lemma FactorialBounds(n: nat)
    ensures factorial(n) >= 1
{
    if n == 0 {
    } else {
        FactorialBounds(n - 1);
    }
}

lemma PermutationProperty(p: seq<int>, original: seq<int>)
    requires multiset(p) == multiset(original) && |p| == |original|
    ensures IsPermutation(p, original)
{
}

lemma MultisetEqualImpliesPermutation(p: seq<int>, original: seq<int>)
    requires |p| == |original| && multiset(p) == multiset(original)
    ensures IsPermutation(p, original)
{
}

function insertAt<T>(s: seq<T>, index: int, elem: T): seq<T>
    requires 0 <= index <= |s|
    ensures |insertAt(s, index, elem)| == |s| + 1
    ensures insertAt(s, index, elem)[index] == elem
    ensures forall i :: 0 <= i < index ==> insertAt(s, index, elem)[i] == s[i]
    ensures forall i :: index <= i < |s| ==> insertAt(s, index, elem)[i + 1] == s[i]
{
    s[0..index] + [elem] + s[index..]
}

lemma InsertAtPreservesMultiset<T>(s: seq<T>, index: int, elem: T)
    requires 0 <= index <= |s|
    ensures multiset(insertAt(s, index, elem)) == multiset(s) + multiset{elem}
{
}

lemma InsertAtLength<T>(s: seq<T>, index: int, elem: T)
    requires 0 <= index <= |s|
    ensures |insertAt(s, index, elem)| == |s| + 1
{
}

ghost method InsertAtProperties<T>(s: seq<T>, index: int, elem: T)
    requires 0 <= index <= |s|
    ensures insertAt(s, index, elem)[index] == elem
    ensures forall i :: 0 <= i < index ==> insertAt(s, index, elem)[i] == s[i]
    ensures forall i :: index <= i < |s| ==> insertAt(s, index, elem)[i + 1] == s[i]
{
}

lemma InsertAtBoundsLemma<T>(s: seq<T>, index: int)
    requires 0 <= index <= |s|
{
}

lemma InsertAtPermutationLemma(p: seq<int>, x: int, nums: seq<int>, index: int)
    requires IsPermutation(p, nums) && 0 <= index <= |p|
    requires AllDistinct(nums)
    ensures IsPermutation(insertAt(p, index, x), nums + [x])
{
    var p_set := multiset(p);
    var nums_set := multiset(nums);
    assert p_set == nums_set;
    
    var inserted := insertAt(p, index, x);
    InsertAtPreservesMultiset(p, index, x);
    assert multiset(inserted) == p_set + multiset{x};
    assert multiset(inserted) == nums_set + multiset{x};
    assert multiset(inserted) == multiset(nums + [x]);
    
    assert |inserted| == |p| + 1;
    assert |nums + [x]| == |nums| + 1;
    assert |inserted| == |nums + [x]|;
    
    MultisetEqualImpliesPermutation(inserted, nums + [x]);
}

lemma LengthPreservedForPermutations(permsOfRest: seq<seq<int>>, rest: seq<int>)
    requires forall p :: p in permsOfRest ==> IsPermutation(p, rest)
    ensures forall j :: 0 <= j < |permsOfRest| ==> |permsOfRest[j]| == |rest|
{
    var i := 0;
    while i < |permsOfRest|
        invariant i <= |permsOfRest|
        invariant forall j :: 0 <= j < i ==> |permsOfRest[j]| == |rest|
    {
        assert |permsOfRest[i]| == |rest|;
        i := i + 1;
    }
}

lemma AllDistinctInsertAt<T>(s: seq<T>, index: int, elem: T)
    requires AllDistinct(s) && 0 <= index <= |s|
    requires !(elem in s)
    ensures AllDistinct(insertAt(s, index, elem))
{
}

lemma InsertAtDifferentPositionsDistinct<T>(s: seq<T>, x: T, j: int, k: int)
    requires AllDistinct(s) && !(x in s)
    requires 0 <= j <= |s| && 0 <= k <= |s| && j != k
    ensures insertAt(s, j, x) != insertAt(s, k, x)
{
}

lemma PermutationsDistinct(permsOfRest: seq<seq<int>>, x: int)
    requires AllDistinct(permsOfRest)
    requires forall p :: p in permsOfRest ==> AllDistinct(p) && !(x in p)
    requires forall p1, p2 :: p1 in permsOfRest && p2 in permsOfRest && p1 != p2 ==> p1 != p2
    ensures forall p :: p in permsOfRest ==> forall j, k :: 0 <= j <= |p| && 0 <= k <= |p| && j != k ==> insertAt(p, j, x) != insertAt(p, k, x)
{
}
// </vc-helpers>
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
        var x := nums[0];
        var rest := nums[1..];
        var permsOfRest: seq<seq<int>>;
        permsOfRest := permute(rest);
        
        result := [];
        var i := 0;
        
        LengthPreservedForPermutations(permsOfRest, rest);
        FactorialBounds(|rest|);
        assert |permsOfRest| == factorial(|rest|);
        
        while i < |permsOfRest|
            invariant i <= |permsOfRest|
            invariant |result| == i * (|rest| + 1)
            invariant forall p :: p in result ==> IsPermutation(p, nums)
            invariant AllDistinct(result)
            invariant forall j :: 0 <= j < i ==> forall k :: 0 <= k <= |rest| ==> 
                insertAt(permsOfRest[j], k, x) in result
        {
            var currentPerm := permsOfRest[i];
            assert |currentPerm| == |rest|;
            assert AllDistinct(currentPerm);
            assert !(x in currentPerm);
            var j := 0;
            
            while j <= |rest|
                invariant j <= |rest| + 1
                invariant |result| == i * (|rest| + 1) + j
                invariant forall p :: p in result ==> IsPermutation(p, nums)
                invariant AllDistinct(result)
                invariant forall k :: 0 <= k < j ==> insertAt(currentPerm, k, x) in result
            {
                InsertAtBoundsLemma(currentPerm, j);
                var newPerm := insertAt(currentPerm, j, x);
                
                InsertAtPermutationLemma(currentPerm, x, rest, j);
                assert IsPermutation(newPerm, nums);
                
                AllDistinctInsertAt(currentPerm, j, x);
                assert AllDistinct(newPerm);
                
                result := result + [newPerm];
                
                j := j + 1;
            }
            
            i := i + 1;
        }
    }
}
// </vc-code>

