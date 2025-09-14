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
  requires 0 <= low <= high
  requires low * low <= n
  requires high * high > n || high == n + 1
  ensures isqrt_helper(n, low, high) >= 0
  ensures isqrt_helper(n, low, high) * isqrt_helper(n, low, high) <= n
  ensures (isqrt_helper(n, low, high) + 1) * (isqrt_helper(n, low, high) + 1) > n
  decreases high - low
{
  if low + 1 >= high then
    low
  else
    var mid := (low + high) / 2;
    if mid * mid <= n then
      isqrt_helper(n, mid, high)
    else
      isqrt_helper(n, low, mid)
}

lemma isqrt_helper_correspondence(n: int, low: int, high: int)
  requires n >= 0
  requires 0 <= low < high
  requires low * low <= n
  requires high * high > n || high == n + 1
  ensures low + 1 >= high ==> isqrt_helper(n, low, high) == low
  ensures low + 1 < high ==> 
    var mid := (low + high) / 2;
    if mid * mid <= n then
      isqrt_helper(n, low, high) == isqrt_helper(n, mid, high)
    else
      isqrt_helper(n, low, high) == isqrt_helper(n, low, mid)
  decreases high - low
{
}

method isqrt_method(n: int) returns (res: int)
  requires n >= 0
  ensures res == isqrt(n)
  ensures res >= 0
  ensures res * res <= n
  ensures (res + 1) * (res + 1) > n
{
  if n == 0 {
    res := 0;
  } else if n == 1 {
    res := 1;
  } else if n <= 3 {
    res := 1;
  } else {
    var guess := n / 2;
    var low := 0;
    var high := guess + 1;
    
    while low + 1 < high
      invariant 0 <= low < high
      invariant low * low <= n
      invariant high * high > n || high == n + 1
      invariant isqrt_helper(n, low, high) == isqrt_helper(n, 0, guess + 1)
      decreases high - low
    {
      var mid := (low + high) / 2;
      isqrt_helper_correspondence(n, low, high);
      if mid * mid <= n {
        low := mid;
      } else {
        high := mid;
      }
    }
    
    res := low;
    assert res == isqrt_helper(n, low, high);
    assert res == isqrt_helper(n, 0, guess + 1);
    assert res == isqrt(n);
  }
}

lemma ComputeExpectedResultCorrect(n: int, sqrt_val: int, x: int, y: int, xed: int, yed: int)
  requires ValidInput(n)
  requires sqrt_val == isqrt(8*n + 1)
  requires x == (sqrt_val - 1) / 2
  requires y == x + 1
  requires xed == x * (x - 1) / 2 + n - x
  requires yed == 2 * (n - y)
  ensures (if xed > yed then xed else yed) == ComputeExpectedResult(n)
{
  var quad_solv_numerator := sqrt_val - 1;
  assert x == quad_solv_numerator / 2;
  assert y == x + 1;
  var ybr := n - y;
  assert yed == 2 * ybr;
  assert ComputeExpectedResult(n) == (if xed > yed then xed else yed);
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
  var sqrt_val := isqrt_method(8*n + 1);
  
  var quad_solv_numerator := sqrt_val - 1;
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
  
  ComputeExpectedResultCorrect(n, sqrt_val, x, y, xed, yed);
}
// </vc-code>

