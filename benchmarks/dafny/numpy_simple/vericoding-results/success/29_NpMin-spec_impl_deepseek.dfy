// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minInRange(a: array<int>, low: int, high: int): (minVal: int)
  requires 0 <= low < high <= a.Length
  reads a
  decreases high - low
  ensures exists i :: low <= i < high && minVal == a[i]
  ensures forall i :: low <= i < high ==> minVal <= a[i]
{
  if low + 1 == high then
    a[low]
  else
    var mid := (low + high) / 2;
    var leftMin := minInRange(a, low, mid);
    var rightMin := minInRange(a, mid, high);
    if leftMin <= rightMin then leftMin else rightMin
}
// </vc-helpers>

// <vc-spec>
method min(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added helper function call with proper termination */
  result := minInRange(a, 0, a.Length);
}
// </vc-code>
