// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed termination with proper decreases clause */
function FindFirstGreaterEqual(xs: seq<int>, target: int, low: int, high: int): (r: int)
  requires 0 <= low <= high + 1
  requires high < |xs|
  requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
  ensures low <= r <= high + 1
  ensures forall i :: low <= i < r ==> xs[i] < target
  ensures r <= high ==> xs[r] >= target
  decreases high - low
{
  if low > high then
    high + 1
  else
    var mid := (low + high) / 2;
    if xs[mid] < target then
      FindFirstGreaterEqual(xs, target, mid + 1, high)
    else
      FindFirstGreaterEqual(xs, target, low, mid - 1)
}
// </vc-helpers>

// <vc-spec>
method SearchInsert(xs: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures 0 <= result <= xs.Length
    ensures forall i :: 0 <= i < result ==> xs[i] < target
    ensures result < xs.Length ==> target <= xs[result]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed implementation to handle all cases */
{
  if xs.Length == 0 {
    result := 0;
  } else {
    result := FindFirstGreaterEqual(xs[..], target, 0, xs.Length - 1);
  }
}
// </vc-code>
