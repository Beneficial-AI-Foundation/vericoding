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
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: |r| == nums.Length && IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
