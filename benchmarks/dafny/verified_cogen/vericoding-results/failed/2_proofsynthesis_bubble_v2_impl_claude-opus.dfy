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
predicate IsPermutation(a: seq<int>, b: seq<int>)
{
    multiset(a) == multiset(b)
}

/* helper modified by LLM (iteration 5): Fixed IndexOf and AdjustIndices verification */
function IndexOf(s: seq<int>, elem: int): nat
    requires elem in s
    ensures 0 <= IndexOf(s, elem) < |s|
    ensures s[IndexOf(s, elem)] == elem
{
    if s[0] == elem then 0 else 1 + IndexOf(s[1..], elem)
}

function AdjustIndices(r: seq<int>, idx: int): seq<int>
    requires forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|
    requires 0 <= idx <= |r|
    ensures |AdjustIndices(r, idx)| == |r|
    ensures forall i :: 0 <= i < |r| ==> 0 <= AdjustIndices(r, idx)[i] <= |r|
    ensures forall i :: 0 <= i < |r| ==> AdjustIndices(r, idx)[i] != idx
    decreases |r|
{
    if |r| == 0 then []
    else 
        var tail := AdjustIndices(r[1..], idx);
        [if r[0] < idx then r[0] else r[0] + 1] + tail
}

function BuildReorder(a: seq<int>, b: seq<int>): seq<int>
    requires IsPermutation(a, b)
    ensures |BuildReorder(a, b)| == |a|
    ensures forall i :: 0 <= i < |a| ==> 0 <= BuildReorder(a, b)[i] < |a|
    ensures forall i, j :: 0 <= i < j < |a| ==> BuildReorder(a, b)[i] != BuildReorder(a, b)[j]
    ensures forall i :: 0 <= i < |a| ==> a[i] == b[BuildReorder(a, b)[i]]
    decreases |a|
{
    if |a| == 0 then []
    else
        var elem := a[0];
        assert elem in b by { assert elem in multiset(b); }
        var idx := IndexOf(b, elem);
        var a' := a[1..];
        var b' := b[..idx] + b[idx+1..];
        assert |b'| == |b| - 1;
        assert |a'| == |a| - 1;
        assert multiset(a') == multiset(a) - multiset{elem};
        assert multiset(b') == multiset(b) - multiset{b[idx]};
        assert b[idx] == elem;
        assert multiset(b') == multiset(b) - multiset{elem};
        assert IsPermutation(a', b');
        var r' := BuildReorder(a', b');
        assert forall i :: 0 <= i < |r'| ==> 0 <= r'[i] < |b'|;
        assert |b'| == |a'|;
        var adjusted := AdjustIndices(r', idx);
        [idx] + adjusted
}

lemma PermutationImpliesReorder(a: seq<int>, b: seq<int>)
    requires IsPermutation(a, b)
    ensures exists r :: IsReorderOf(r, a, b)
{
    var r := BuildReorder(a, b);
    assert |r| == |a| == |b|;
    assert forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|;
    assert forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j];
    assert forall i :: 0 <= i < |a| ==> a[i] == b[r[i]];
    var p := seq(|r|, i requires 0 <= i < |r| => b[r[i]]);
    assert p == a;
    assert IsReorderOf(r, a, b);
}

method BubbleSort(a: array<int>)
    modifies a
    ensures SortedBetween(a[..], 0, a.Length)
    ensures IsPermutation(a[..], old(a[..]))
{
    var n := a.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant SortedBetween(a[..], n - i, n)
        invariant forall j, k :: 0 <= j < n - i <= k < n ==> a[j] <= a[k]
        invariant IsPermutation(a[..], old(a[..]))
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j < n - i
            invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
            invariant SortedBetween(a[..], n - i, n)
            invariant forall k, l :: 0 <= k < n - i <= l < n ==> a[k] <= a[l]
            invariant IsPermutation(a[..], old(a[..]))
        {
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
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
    /* code modified by LLM (iteration 5): Use BubbleSort and prove reorder exists */
    BubbleSort(nums);
    assert IsPermutation(nums[..], old(nums[..]));
    PermutationImpliesReorder(nums[..], old(nums[..]));
}
// </vc-code>
