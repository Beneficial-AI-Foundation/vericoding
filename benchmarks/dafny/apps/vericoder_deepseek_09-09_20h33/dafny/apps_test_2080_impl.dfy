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
lemma isqrt_helper(n: int, low: int, high: int) returns (result: int)
  requires n >= 0
  requires low >= 0 && high >= 0
  requires low * low <= n && high * high > n
  requires low <= high
  ensures result >= 0
  ensures result * result <= n
  ensures (result + 1) * (result + 1) > n
  decreases high - low
{
  if low + 1 >= high {
    result := low;
  } else {
    var mid := low + (high - low) / 2;
    var mid_sq := mid * mid;
    if mid_sq <= n {
      result := isqrt_helper(n, mid, high);
    } else {
      result := isqrt_helper(n, low, mid);
    }
  }
}

lemma isqrt_correct(n: int)
  requires n >= 0
  ensures isqrt(n) >= 0
  ensures isqrt(n) * isqrt(n) <= n
  ensures (isqrt(n) + 1) * (isqrt(n) + 1) > n
{
  if n == 0 {
  } else if n == 1 {
  } else if n <= 3 {
  } else {
    var guess := n / 2;
    var low := 0;
    var high := guess + 1;
    var res := isqrt_helper(n, low, high);
    assert res == isqrt(n);
  }
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
  var temp := 8 * n + 1;
  assert temp >= 0 by {
    assert 8 * n + 1 >= 1;
  }
  var sqrt_temp := isqrt(temp);
  isqrt_correct(temp);
  var quad_solv_numerator := sqrt_temp - 1;
  var x := quad_solv_numerator / 2;
  var y := x + 1;
  var xed := x * (x - 1) / 2 + n - x;
  var ybr := n - y;
  var yed := 2 * ybr;
  if xed > yed {
    result := xed;
  } else {
    result := yed;
  }
}
// </vc-code>

