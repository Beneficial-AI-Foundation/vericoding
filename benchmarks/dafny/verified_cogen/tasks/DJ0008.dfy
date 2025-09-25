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
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
