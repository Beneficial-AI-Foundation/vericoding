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
    /* code modified by LLM (iteration 3): implemented min-finding and swapping inline to avoid unimplemented helpers */
    if a.Length == 0 {
        return new int[0];
    }
    result := new int[a.Length];
    for k := 0 to a.Length
    {
        result[k] := a[k];
    }
    for i := 0 to a.Length-1
        invariant 0 <= i <= a.Length-1
        invariant forall j, k :: 0 <= j <= k < i ==> result[j] <= result[k]
        invariant forall j :: 0 <= j < i ==> forall k :: i <= k < a.Length ==> result[j] <= result[k]
        invariant multiset(result[..]) == multiset(a[..])
    {
        // Find the min index in the range [i, a.Length-1]
        var minIndex := i;
        var j := i;
        while j < a.Length
            invariant i <= minIndex < a.Length && i <= j <= a.Length
            invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
        {
            if result[j] < result[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }

        // Swap result[i] and result[minIndex]
        var temp := result[i];
        result[i] := result[minIndex];
        result[minIndex] := temp;
    }
}
// </vc-code>
