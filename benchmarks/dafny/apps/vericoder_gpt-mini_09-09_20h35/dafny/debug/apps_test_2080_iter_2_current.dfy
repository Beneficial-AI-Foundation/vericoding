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

// <vc-helpers>
function isqrt_helper(n: int, low: int, high: int): int
  requires n >= 0
  requires 0 <= low < high
  requires low * low <= n
  decreases high - low
  ensures 0 <= result
  ensures result * result <= n
  ensures (result + 1) * (result + 1) > n
{
  var mid := (low + high) / 2;
  if mid * mid <= n then
    if (mid + 1) * (mid + 1) > n then mid
    else isqrt_helper(n, mid + 1, high)
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
{
  result := ComputeExpectedResult(n);
}
// </vc-code>

