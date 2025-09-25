// <vc-preamble>
predicate ValidInput(n: int) {
  n >= 1 && n <= 1000000
}

predicate ValidResult(result: int) {
  result >= 0 && result < 1000000007
}

function factorial(n: int, m: int): int
  requires n >= 0 && m > 0
  decreases n
{
  if n <= 1 then 1
  else (n * factorial(n-1, m)) % m
}

function factorialLoop(start: int, end: int, m: int): int
  requires start >= 1 && end >= start && m > 0
  decreases end - start
{
  if start >= end then 1
  else (start * factorialLoop(start + 1, end, m)) % m
}

function modInverse(a: int, m: int): int
  requires a > 0 && m > 0
  requires m > 1
  requires a < m
  decreases a
{
  if a == 1 then 1
  else if m % a == 0 then 1
  else ((m - (m / a) * modInverse(m % a, m)) % m)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
  var B := 1000000007;
  var u := 1;
  var f := 1;

  // Compute u = (n+1)!
  var i := 2;
  while i < n + 2
    invariant 2 <= i <= n + 2
    invariant u >= 1
    invariant u == factorialLoop(2, i, B)
    invariant u < B
  {
    u := (u * i) % B;
    i := i + 1;
  }

  // Compute f = (2n+2)!
  i := 2;
  while i < 2*n + 3
    invariant 2 <= i <= 2*n + 3
    invariant f >= 1
    invariant f == factorialLoop(2, i, B)
    invariant f < B
  {
    f := (f * i) % B;
    i := i + 1;
  }

  var inv_u := modInverse(u, B);
  var temp := (f * inv_u) % B;
  temp := (temp * inv_u) % B;
  result := (temp + B - 1) % B;
}
// </vc-code>
