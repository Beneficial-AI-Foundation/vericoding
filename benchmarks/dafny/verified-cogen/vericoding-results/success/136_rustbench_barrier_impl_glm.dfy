// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for array access */
function Max(arr: array<int>, low: int, high: int): int
    requires 0 <= low <= high < arr.Length
    reads arr
    ensures forall i: int :: low <= i <= high ==> arr[i] <= Max(arr, low, high)
    ensures exists i: int :: low <= i <= high && arr[i] == Max(arr, low, high)
    decreases high - low
{
    if low == high then arr[low]
    else
        var m := Max(arr, low, high-1);
        if arr[high] > m then arr[high] else m
}

/* helper modified by LLM (iteration 2): added reads clause for array access */
function Min(arr: array<int>, low: int, high: int): int
    requires 0 <= low <= high < arr.Length
    reads arr
    ensures forall i: int :: low <= i <= high ==> Min(arr, low, high) <= arr[i]
    ensures exists i: int :: low <= i <= high && arr[i] == Min(arr, low, high)
    decreases high - low
{
    if low == high then arr[low]
    else
        var m := Min(arr, low, high-1);
        if arr[high] < m then arr[high] else m
}
// </vc-helpers>

// <vc-spec>
method Barrier(arr: array<int>, p: int) returns (result: bool)
    requires
        arr.Length > 0 &&
        0 <= p < arr.Length
    ensures
        result == forall k, l :: 0 <= k <= p && p < l < arr.Length ==> arr[k] < arr[l]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no changes needed, helper reads clauses added */
  if p == arr.Length - 1 {
    result := true;
  } else {
    result := Max(arr, 0, p) < Min(arr, p+1, arr.Length-1);
  }
}
// </vc-code>
