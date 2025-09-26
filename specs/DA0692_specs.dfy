// <vc-preamble>
const MOD: int := 1000000007

predicate ValidInput(n: int, x: int, pos: int) {
  1 <= x <= n <= 1000 && 0 <= pos <= n - 1
}

function ComputeBinarySearchCounts(n: int, pos: int, left: int, right: int, chk1: int, chk_r: int): (int, int)
  requires 0 <= left <= right <= n
  requires 0 <= pos < n
  requires chk1 >= 0 && chk_r >= 0
  ensures var (res1, res2) := ComputeBinarySearchCounts(n, pos, left, right, chk1, chk_r); res1 >= 0 && res2 >= 0
  decreases right - left
{
  if left >= right then
    (chk1, chk_r)
  else
    var middle := (left + right) / 2;
    if middle <= pos then
      if middle < pos then
        ComputeBinarySearchCounts(n, pos, middle + 1, right, chk1 + 1, chk_r)
      else
        ComputeBinarySearchCounts(n, pos, middle + 1, right, chk1, chk_r)
    else
      ComputeBinarySearchCounts(n, pos, left, middle, chk1, chk_r + 1)
}

predicate ValidResult(n: int, x: int, pos: int, result: int)
  requires ValidInput(n, x, pos)
{
  var (chk1, chk_r) := ComputeBinarySearchCounts(n, pos, 0, n, 0, 0);
  0 <= result < MOD &&
  ((chk1 > x - 1 || chk_r > n - x) ==> result == 0) &&
  ((chk1 <= x - 1 && chk_r <= n - x && chk1 + chk_r + 1 <= n) ==> 
    result == (f(x - 1, chk1) * f(n - x, chk_r) % MOD * f(n - chk1 - chk_r - 1, n - chk1 - chk_r - 1)) % MOD)
}
// </vc-preamble>

// <vc-helpers>
function f(n: int, cnt: int): int
  requires n >= 0 && cnt >= 0
  decreases cnt
{
  if cnt == 0 then 1
  else if n <= 0 then 0
  else (f(n-1, cnt-1) * n) % MOD
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, x: int, pos: int) returns (result: int)
  requires ValidInput(n, x, pos)
  ensures ValidResult(n, x, pos, result)
// </vc-spec>
// <vc-code>
{
  var chk1 := 0;
  var chk_r := 0;
  var left := 0;
  var right := n;

  while left < right
    invariant 0 <= left <= right <= n
    invariant chk1 >= 0 && chk_r >= 0
    invariant ComputeBinarySearchCounts(n, pos, 0, n, 0, 0) == ComputeBinarySearchCounts(n, pos, left, right, chk1, chk_r)
    decreases right - left
  {
    var middle := (left + right) / 2;
    if middle <= pos {
      if middle < pos {
        chk1 := chk1 + 1;
      }
      left := middle + 1;
    } else {
      chk_r := chk_r + 1;
      right := middle;
    }
  }

  if chk1 > x - 1 || chk_r > n - x {
    result := 0;
  } else {
    var rest := n - chk1 - chk_r - 1;
    assert x - 1 >= 0 && chk1 >= 0;
    assert n - x >= 0 && chk_r >= 0;
    if rest >= 0 {
      result := (f(x - 1, chk1) * f(n - x, chk_r) % MOD * f(rest, rest)) % MOD;
    } else {
      result := 0;
    }
  }
}
// </vc-code>
