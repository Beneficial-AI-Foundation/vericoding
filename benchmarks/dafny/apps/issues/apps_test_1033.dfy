// <vc-preamble>
function get(x: int, k: int): int
  requires k > 0
  requires x >= 0
{
  if x <= k then
    x * (x + 1) / 2
  else
    var res := k * x - k * (k - 1) / 2;
    var sz := x - k - 1;
    if sz % 2 == 0 then
      var cnt := sz / 2;
      res + (2 + sz) * cnt / 2
    else
      var cnt := sz / 2 + 1;
      res + (1 + sz) * cnt / 2
}

predicate ValidInput(n: int, k: int)
{
  n > 0 && k > 0 && n <= get(1000000000000000000, k)
}

predicate ValidResult(result: int, n: int, k: int)
  requires k > 0
  requires result >= 0
{
  result > 0 && 
  get(result, k) >= n && 
  (result == 1 || get(result - 1, k) < n) && 
  result <= 1000000000000000000
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result >= 0
  ensures ValidResult(result, n, k)
// </vc-spec>
// <vc-code>
{
  var l: int := 0;
  var r: int := 1000000000000000000;

  while r - l > 1
    invariant 0 <= l < r
    invariant get(l, k) < n
    invariant get(r, k) >= n
    invariant r <= 1000000000000000000
  {
    var mid: int := l + (r - l) / 2;
    if get(mid, k) >= n {
      r := mid;
    } else {
      l := mid;
    }
  }

  result := r;
}
// </vc-code>
