// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
{
    forall i, j :: from <= i < j < to && 0 <= i < |a| && 0 <= j < |a| ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && p == seq(|r|, i requires 0 <= i < |r| => s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add HelperLemma to maintain the permutation invariant */
lemma SwapMaintainsPermutation<T>(a: seq<T>, i: int, j: int)
    requires 0 <= i < |a|
    requires 0 <= j < |a|
    ensures exists r :: IsReorderOf(r, a[i := a[j], j := a[i]], a)
{
    var b := a[i := a[j], j := a[i]];
    var id := seq(|a|, k => k);
    var r := id;
    if i != j {
        r := id[i := j, j := i];
    }
    assert IsReorderOf(r, b, a);
}
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `IsReorderOf` invariant logic and `SortedBetween` postcondition */
{
    var N := nums.Length;
    if N == 0 {
        return;
    }
    
    var old_nums_seq := nums[..];

    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant (forall k, l :: 0 <= k < l < i ==> nums[k] <= nums[l]) // nums[0..i-1] is sorted
        invariant (exists r :: IsReorderOf(r, nums[..], old_nums_seq))
    {
        var j := i;
        while j > 0 && nums[j-1] > nums[j]
            invariant 0 <= j <= i
            invariant (forall k, l :: 0 <= k < l < j ==> nums[k] <= nums[l])
            invariant (forall k, l :: j <= k < l < i ==> nums[k] <= nums[l])
            invariant (exists r_current :: IsReorderOf(r_current, nums[..], old_nums_seq))
        {
            var temp := nums[j];
            nums[j] := nums[j-1];
            nums[j-1] := temp;
            SwapMaintainsPermutation(nums[..], j-1, j);
            j := j - 1;
        }
        i := i + 1;
    }
    assert SortedBetween(nums[..], 0, N);
}
// </vc-code>
