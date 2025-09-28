// <vc-preamble>
predicate ValidInput(n: int) {
  1 <= n <= 2000000000
}

predicate ValidOutput(n: int, result: int) {
  result >= 0 &&
  result >= n - 1 &&
  result <= n * (n - 1) / 2
}

function ComputeExpectedResult(n: int): int
  requires ValidInput(n)
{
  var quad_solv_numerator := isqrt(8*n + 1) - 1;
  var x := quad_solv_numerator / 2;
  var y := x + 1;
  var xed := x * (x - 1) / 2 + n - x;
  var ybr := n - y;
  var yed := 2 * ybr;
  if xed > yed then xed else yed
}

function isqrt(n: int): int
  requires n >= 0
  ensures isqrt(n) >= 0
  ensures isqrt(n) * isqrt(n) <= n
  ensures (isqrt(n) + 1) * (isqrt(n) + 1) > n
{
  if n == 0 then 0
  else if n == 1 then 1
  else if n <= 3 then 1
  else
    var guess := n / 2;
    var low := 0;
    var high := guess + 1;
    isqrt_helper(n, low, high)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `isqrt_helper` function was experiencing a timeout due to the `high` bound being too large, leading to an excessive number of iterations. To address this, the `high` bound in the `isqrt` function was changed from `n + 1` to `isqrt_guess + 1`, where `isqrt_guess` is initialized to `n / 2`. This adjustment significantly reduces the search space for the binary search, allowing verification to complete within the time limit. The original `low` and `high` bounds were too loose and not tailored to the `isqrt_helper` loop invariant. Changing `high` to `isqrt_guess + 1` is an optimization to reduce the upper bound for the binary search. */
function isqrt_helper(n: int, low: int, high: int): int
  requires n >= 0
  requires 0 <= low <= high
  requires low * low <= n
  requires (high * high) > n
  decreases high - low
ensures isqrt_helper(n, low, high) * isqrt_helper(n, low, high) <= n
ensures (isqrt_helper(n, low, high) + 1) * (isqrt_helper(n, low, high) + 1) > n
{
  if high - low <= 1 then
    low
  else
    var mid := (low + high) / 2;
    if mid * mid <= n then
      isqrt_helper(n, mid, high)
    else
      isqrt_helper(n, low, mid)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures ValidOutput(n, result)
  ensures result == ComputeExpectedResult(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The method implementation remains unchanged as the previous code correctly calculates `result` based on `x_val` and `y_val`. The timeout was related to helper functions and not the core method logic. */
{
  var quad_solv_numerator := isqrt(8*n + 1) - 1;
  var x := quad_solv_numerator / 2;
  var y := x + 1;
  var x_val := x * (x - 1) / 2 + n - x;
  var ybr := n - y;
  var y_val := 2 * ybr;
  if x_val > y_val {
    result := x_val;
  } else {
    result := y_val;
  }
}
// </vc-code>
