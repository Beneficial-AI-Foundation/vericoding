// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause for termination in recursive Max and Min functions */
function Max(a: array<int>, low: int, high: int): int
  reads a
  requires 0 <= low <= high < a.Length
  ensures forall i :: low <= i <= high ==> a[i] <= Max(a, low, high)
  ensures exists i :: low <= i <= high && a[i] == Max(a, low, high)
  decreases high - low
{
  if low == high then a[low] else if Max(a, low+1, high) <= a[low] then a[low] else Max(a, low+1, high)
}

function Min(a: array<int>, low: int, high: int): int
  reads a
  requires 0 <= low <= high < a.Length
  ensures forall i :: low <= i <= high ==> Min(a, low, high) <= a[i]
  ensures exists i :: low <= i <= high && a[i] == Min(a, low, high)
  decreases high - low
{
  if low == high then a[low] else if Min(a, low+1, high) >= a[low] then a[low] else Min(a, low+1, high)
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
  /* code modified by LLM (iteration 4): implemented method body using Max and Min helper functions */
  result := if p + 1 >= arr.Length then true else Max(arr, 0, p) < Min(arr, p+1, arr.Length-1);
}
// </vc-code>
