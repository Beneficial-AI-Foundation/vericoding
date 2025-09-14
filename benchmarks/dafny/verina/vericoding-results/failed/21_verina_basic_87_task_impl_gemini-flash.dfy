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
/* helper modified by LLM (iteration 5): Adding the FindMinIndexInRange function as a helper */
function FindMinIndexInRange(arr: array<int>, start: int, finish: int): int
    requires start <= finish
    requires finish <= arr.Length
    requires start < arr.Length
    ensures start <= result < finish
{
    var result := start;
    var j := start + 1;
    while j < finish
        invariant start <= result < j
        invariant forall k :: start <= k < j ==> arr[result] <= arr[k]
        invariant start <= j <= finish
    {
        if arr[j] < arr[result] {
            result := j;
        }
        j := j + 1;
    }
    return result;
}

/* helper modified by LLM (iteration 5): Adding the Swap method as a helper */
method Swap(a: array<int>, i: int, j: int)
    requires a.Length > 0
    requires 0 <= i < a.Length
    requires 0 <= j < a.Length
    modifies a
    ensures a.Length == old(a.Length)
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
    ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
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
/* code modified by LLM (iteration 5): Correcting loop invariants in SelectionSort to satisfy verification conditions. Specifically, the invariant `multiset(result[..]) == multiset(a[..])` was failing because the `Swap` operation was not correctly reflected in the multiset until `Swap` was also defined as a helper. Also, the `forall k :: 0 <= k < i ==> (forall l :: i <= l < result.Length ==> result[k] <= result[l])` invariant was failing because it was not directly implied by the initial state of the loop and the `Swap` operation. Simplified the final invariant to capture the sorted prefix correctly. */
{
    if a.Length == 0 {
        return new int[0];
    }

    result := new int[a.Length];
    for k := 0 to a.Length - 1 {
        result[k] := a[k];
    }

    var i := 0;
    while i < result.Length
        invariant 0 <= i <= result.Length
        invariant forall p, q :: 0 <= p < q < i ==> result[p] <= result[q]
        invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < result.Length ==> result[k] <= result[l])
        invariant multiset(result[..]) == multiset(a[..])
    {
        var minIndex: int := FindMinIndexInRange(result, i, result.Length);
        if minIndex != i {
            Swap(result, i, minIndex);
        }
        i := i + 1;
    }
    return result;
}
// </vc-code>
