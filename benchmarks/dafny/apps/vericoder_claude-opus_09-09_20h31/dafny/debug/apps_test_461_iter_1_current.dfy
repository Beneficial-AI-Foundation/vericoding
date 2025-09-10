predicate ValidInput(n: int, a: int, b: int, c: int)
{
  1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

function MinDistance(n: int, a: int, b: int, c: int): int
  requires ValidInput(n, a, b, c)
  ensures MinDistance(n, a, b, c) >= 0
  ensures n == 1 ==> MinDistance(n, a, b, c) == 0
{
  if n == 1 then 0
  else (n - 1) * min(a, b)
}

function min(x: int, y: int): int
{
  if x <= y then x else y
}

function max(x: int, y: int): int
{
  if x >= y then x else y
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int) returns (result: int)
  requires ValidInput(n, a, b, c)
  ensures result >= 0
  ensures n == 1 ==> result == 0
  ensures result <= (n-1) * max(a, max(b, c))
  ensures result == MinDistance(n, a, b, c)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := 0;
  } else {
    result := (n - 1) * min(a, b);
  }
}
// </vc-code>

