// <vc-preamble>

predicate ValidInput(arr: seq<int>) {
    forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
}

predicate HasDecreaseAt(arr: seq<int>, i: int) {
    1 <= i < |arr| && arr[i] < arr[i-1]
}

predicate IsLargestDecreaseIndex(arr: seq<int>, result: int) {
    HasDecreaseAt(arr, result) && 
    (forall j :: result < j < |arr| ==> arr[j] >= arr[j-1])
}

predicate IsNonDecreasing(arr: seq<int>) {
    forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i-1]
}
// </vc-preamble>

// <vc-helpers>

method helper_FindLastDecrease(arr: seq<int>) returns (index: int)
    requires ValidInput(arr)
    requires |arr| > 1
    requires exists i :: 1 <= i < |arr| && arr[i] < arr[i-1]
    ensures 0 < index < |arr|
    ensures HasDecreaseAt(arr, index)
    ensures forall j :: index < j < |arr| ==> arr[j] >= arr[j-1]
{
    var i := |arr| - 1;
    while i >= 1
        invariant 0 <= i <= |arr| - 1
        invariant forall j :: i < j < |arr| ==> arr[j] >= arr[j-1]
    {
        if arr[i] < arr[i-1] {
            index := i;
            return;
        }
        i := i - 1;
    }
}

/* helper modified by LLM (iteration 3): Added helper to find last decrease with proper ensures */
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result == -1 || (0 < result < |arr|)
    ensures result == -1 ==> IsNonDecreasing(arr)
    ensures result != -1 ==> IsLargestDecreaseIndex(arr, result)
    ensures result != -1 ==> (exists i :: HasDecreaseAt(arr, i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Use helper to find last decrease and handle all cases */
    if |arr| < 2 {
        result := -1;
        return;
    }
    
    if IsNonDecreasing(arr) {
        result := -1;
        return;
    }
    
    // Call helper to find the last decrease index
    result := helper_FindLastDecrease(arr);
}
// </vc-code>
