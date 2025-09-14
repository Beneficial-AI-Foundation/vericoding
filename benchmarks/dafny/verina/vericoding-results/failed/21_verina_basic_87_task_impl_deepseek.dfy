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
/* helper modified by LLM (iteration 5): Fixed FindMinIndexInRange and Swap implementations */
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish &&
        forall k :: start <= k < finish ==> arr[result] <= arr[k]
{
    result := start;
    var idx: int := start + 1;
    while idx < finish
        invariant start <= idx <= finish
        invariant start <= result < finish
        invariant forall k :: start <= k < idx ==> arr[result] <= arr[k]
    {
        if arr[idx] < arr[result] {
            result := idx;
        }
        idx := idx + 1;
    }
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        a[i] == old(a[j]) &&
        a[j] == old(a[i]) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    var temp: int := a[i];
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
/* code modified by LLM (iteration 5): Fixed verification errors with refined invariants */
{
    result := new int[a.Length];
    var k: int := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall i :: 0 <= i < k ==> result[i] == a[i]
    {
        result[k] := a[k];
        k := k + 1;
    }
    
    var i: int := 0;
    
    while i < result.Length
        invariant 0 <= i <= result.Length
        invariant forall x, y :: 0 <= x <= y < i ==> result[x] <= result[y]
        invariant multiset(result[..]) == multiset(a[..])
        invariant forall x :: 0 <= x < i ==> forall y :: i <= y < result.Length ==> result[x] <= result[y]
    {
        if i < result.Length - 1 {
            var minIdx := FindMinIndexInRange(result, i, result.Length);
            if minIdx != i {
                Swap(result, i, minIdx);
            }
        }
        i := i + 1;
    }
}
// </vc-code>
