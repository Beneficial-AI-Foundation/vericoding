// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added decreases clause to SubarraySum for termination */
function SubarraySum(arr: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start == end then 0
  else arr[start] + SubarraySum(arr, start + 1, end)
}

function MaxSubarraySumWithLengthDivisibleByK(arr: array<int>, k: int, i: int): int
  requires k > 0
  requires 0 <= i <= arr.Length
  reads arr
  decreases arr.Length - i
{
  if i == arr.Length then
    -2147483648
  else
    var maxFromI := MaxSubarraySumFromIndex(arr, k, i, i + k);
    var maxFromRest := MaxSubarraySumWithLengthDivisibleByK(arr, k, i + 1);
    if maxFromI > maxFromRest then maxFromI else maxFromRest
}

function MaxSubarraySumFromIndex(arr: array<int>, k: int, start: int, end: int): int
  requires k > 0
  requires 0 <= start <= arr.Length
  requires start <= end
  reads arr
  decreases arr.Length - end + start
{
  if end > arr.Length then
    -2147483648
  else if (end - start) % k == 0 && end - start > 0 then
    var sum := SubarraySum(arr, start, end);
    var restMax := MaxSubarraySumFromIndex(arr, k, start, end + k);
    if sum > restMax then sum else restMax
  else
    MaxSubarraySumFromIndex(arr, k, start, end + k)
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySumDivisibleByK(arr: array<int>, k: int) returns (result: int)
    requires k > 0
    ensures true // TODO: Add postcondition based on subarrays with length divisible by k
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): No changes needed, reusing working implementation */
  if arr.Length == 0 {
    result := -2147483648;
  } else {
    result := MaxSubarraySumWithLengthDivisibleByK(arr, k, 0);
    if result == -2147483648 {
      result := 0;
    }
  }
}
// </vc-code>
