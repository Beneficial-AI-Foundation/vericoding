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
/* helper modified by LLM (iteration 5): removed unnecessary type parameter and improved verification with simpler bubble sort */
function IdentityReorder(n: int): seq<int>
    requires n >= 0
    ensures |IdentityReorder(n)| == n
    ensures forall i :: 0 <= i < n ==> 0 <= IdentityReorder(n)[i] < n
    ensures forall i, j :: 0 <= i < j < n ==> IdentityReorder(n)[i] != IdentityReorder(n)[j]
    ensures forall i :: 0 <= i < n ==> IdentityReorder(n)[i] == i
{
    seq(n, i requires 0 <= i < n => i)
}

lemma IdentityReorderCorrect<T>(s: seq<T>)
    ensures IsReorderOf(IdentityReorder(|s|), s, s)
{
    var r := IdentityReorder(|s|);
    assert |r| == |s|;
    assert forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|;
    assert forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j];
    assert s == seq(|r|, i requires 0 <= i < |r| => s[r[i]]);
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
    /* code modified by LLM (iteration 5): simplified sorting with direct implementation */
    var n := nums.Length;
    if n <= 1 {
        IdentityReorderCorrect(old(nums[..]));
        return;
    }
    
    IdentityReorderCorrect(old(nums[..]));
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant exists r :: IsReorderOf(r, nums[..], old(nums[..]))
    {
        var j := i + 1;
        while j < n
            invariant i < j <= n
            invariant exists r :: IsReorderOf(r, nums[..], old(nums[..]))
        {
            if nums[i] > nums[j] {
                nums[i], nums[j] := nums[j], nums[i];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
