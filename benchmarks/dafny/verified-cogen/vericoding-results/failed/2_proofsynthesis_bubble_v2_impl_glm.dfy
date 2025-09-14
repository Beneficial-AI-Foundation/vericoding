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
/* helper modified by LLM (iteration 5): fixed precondition to require start < end and removed assertion */
method FindMinIndex(a: array<int>, start: int, end: int) returns (result: int)
    requires 0 <= start < end <= a.Length
    ensures start <= result < end
    ensures forall i :: start <= i < end ==> a[result] <= a[i]
{
    var minIndex := start;
    var i := start + 1;
    while i < end
        invariant start <= minIndex < i <= end
        invariant forall j :: start <= j < i ==> a[minIndex] <= a[j]
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
    return minIndex;
}
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed reordering proof with ghost permutation variable and base case */
    var n := nums.Length;
    if n <= 1 {
        if n == 0 {
            assert exists r :: IsReorderOf(r, nums[..], old(nums[..]));
        } else {
            var r0 := seq(n, i => i);
            assert IsReorderOf(r0, nums[..], old(nums[..]));
        }
        return;
    }
    
    ghost var r := seq(n, i => i);
    var i := 0;
    while i < n - 1
        invariant 0 <= i < n
        invariant SortedBetween(nums[..], 0, i)
        invariant IsReorderOf(r, nums[..], old(nums[..]))
    {
        var minPos := FindMinIndex(nums, i, n);
        var temp := nums[i];
        nums[i] := nums[minPos];
        nums[minPos] := temp;
        
        ghost var tempR := r[i];
        r[i] := r[minPos];
        r[minPos] := tempR;
        
        assert IsReorderOf(r, nums[..], old(nums[..]));
        
        i := i + 1;
    }
}
// </vc-code>
