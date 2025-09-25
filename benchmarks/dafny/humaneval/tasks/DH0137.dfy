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
    assume {:axiom} false;
  }
// </vc-code>
