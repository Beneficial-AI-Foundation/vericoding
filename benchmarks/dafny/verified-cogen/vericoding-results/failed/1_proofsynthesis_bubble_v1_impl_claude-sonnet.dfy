// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
    requires 0 <= from <= to <= |a|
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
    requires |r| == |p| && |r| == |s|
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |s|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && (forall i :: 0 <= i < |r| ==> p[i] == s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): complete identity permutation lemma proof */
lemma IdentityPermutation(a: seq<int>)
    ensures exists r :: |r| == |a| && IsReorderOf(r, a, a)
{
    var identity := seq(|a|, i => i);
    assert |identity| == |a|;
    assert forall i :: 0 <= i < |identity| ==> 0 <= identity[i] < |a|;
    assert forall i, j :: 0 <= i < j < |identity| ==> identity[i] != identity[j];
    assert forall i :: 0 <= i < |identity| ==> a[i] == a[identity[i]];
    assert IsReorderOf(identity, a, a);
}

method BubbleSort(a: array<int>)
    modifies a
    ensures SortedBetween(a[..], 0, a.Length)
    ensures exists r :: |r| == a.Length && IsReorderOf(r, a[..], old(a[..]))
{
    var oldSeq := a[..];
    IdentityPermutation(a[..]);
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant exists r :: |r| == a.Length && IsReorderOf(r, a[..], oldSeq)
    {
        var j := a.Length - 1;
        while j > i
            invariant i <= j < a.Length
            invariant exists r :: |r| == a.Length && IsReorderOf(r, a[..], oldSeq)
        {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: |r| == nums.Length && IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call bubble sort method */
    BubbleSort(nums);
}
// </vc-code>
