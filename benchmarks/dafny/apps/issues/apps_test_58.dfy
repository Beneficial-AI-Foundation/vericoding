// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int)
{
  n >= 1 && a >= 1 && b >= 1 && a <= n && b <= n
}

predicate ValidResult(result: int, n: int, a: int, b: int)
  requires ValidInput(n, a, b)
{
  result >= 0 && result <= 6 && result == woodenBarOptimization(n, a, b, 0, 4, 2)
}
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int
{
  if x <= y then x else y
}

function woodenBarOptimization(n: int, a: int, b: int, left: int, cnta: int, cntb: int): int
  requires n >= 1 && a >= 1 && b >= 1
  requires a <= n && b <= n
  requires cnta >= 0 && cntb >= 0
  requires left >= 0 && left <= n
  ensures cnta == 0 && cntb == 0 ==> woodenBarOptimization(n, a, b, left, cnta, cntb) == 0
  ensures cnta < 0 || cntb < 0 ==> woodenBarOptimization(n, a, b, left, cnta, cntb) >= 1000000000
  ensures cnta >= 0 && cntb >= 0 ==> 
    woodenBarOptimization(n, a, b, left, cnta, cntb) >= 0
  ensures cnta >= 0 && cntb >= 0 ==> 
    woodenBarOptimization(n, a, b, left, cnta, cntb) <= cnta + cntb
  decreases cnta + cntb, cnta, cntb
{
  if cnta == 0 && cntb == 0 then 
    0
  else if cnta < 0 || cntb < 0 then 
    1000000000
  else if a <= left && cnta > 0 && b <= left && cntb > 0 then
    min(woodenBarOptimization(n, a, b, left - a, cnta - 1, cntb),
        woodenBarOptimization(n, a, b, left - b, cnta, cntb - 1))
  else if a <= left && cnta > 0 then
    woodenBarOptimization(n, a, b, left - a, cnta - 1, cntb)
  else if b <= left && cntb > 0 then
    woodenBarOptimization(n, a, b, left - b, cnta, cntb - 1)
  else if cnta > 0 && cntb > 0 then
    1 + min(woodenBarOptimization(n, a, b, n - a, cnta - 1, cntb),
            woodenBarOptimization(n, a, b, n - b, cnta, cntb - 1))
  else if cnta > 0 then
    1 + woodenBarOptimization(n, a, b, n - a, cnta - 1, cntb)
  else if cntb > 0 then
    1 + woodenBarOptimization(n, a, b, n - b, cnta, cntb - 1)
  else
    0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: int)
  requires ValidInput(n, a, b)
  ensures ValidResult(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  result := woodenBarOptimization(n, a, b, 0, 4, 2);
}
// </vc-code>
