// <vc-preamble>
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish
{
    // impl-start
    assume {:axiom} false;
    result := start;
    // impl-end
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == old(a[j])) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[j] == old(a[i])) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added SwapHelper to avoid compilation warning and kept necessary predicates. */
predicate IsSortedUpto(s: seq<int>, i: int)
  requires 0 <= i <= |s|
{
  forall j, k :: 0 <= j <= k < i ==> s[j] <= s[k]
}

predicate IsPartitioned(s: seq<int>, i: int)
  requires 0 <= i <= |s|
{
  forall j, k :: 0 <= j < i <= k < |s| ==> s[j] <= s[k]
}

method SwapHelper(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
    ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): used SwapHelper and fixed inner loop modifies clause */
    result := new int[a.Length];
    var k_copy := 0;
    while k_copy < a.Length
        invariant 0 <= k_copy <= a.Length
        invariant forall i :: 0 <= i < k_copy ==> result[i] == a[i]
        modifies result
    {
        result[k_copy] := a[k_copy];
        k_copy := k_copy + 1;
    }

    assert result[..] == a[..];

    var i: int := 0;
    while i < result.Length
        invariant 0 <= i <= result.Length
        invariant multiset(result[..]) == multiset(a[..])
        invariant IsSortedUpto(result[..], i)
        invariant IsPartitioned(result[..], i)
        modifies result
    {
        var min_idx := i;
        var j := i + 1;
        while j < result.Length
            invariant i <= j <= result.Length
            invariant i <= min_idx < result.Length
            invariant forall k :: i <= k < j ==> result[min_idx] <= result[k]
        {
            if result[j] < result[min_idx] {
                min_idx := j;
            }
            j := j + 1;
        }

        SwapHelper(result, i, min_idx);

        i := i + 1;
    }
}
// </vc-code>
