// The ghost function `sum(n)` computes:
// - `sum(0) = 0`
// - `sum(n) = n + sum(n-1)` for n > 0

// This gives us the sum 1 + 2 + ... + n.

// I'll implement this using a simple loop that accumulates the sum:

ghost function sum(n: nat): int
{
    if n == 0 then 0 else n + sum(n - 1)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Sum(n: nat) returns (s: int)
ensures s == sum(n)
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sum(i)
  {
    i := i + 1;
    s := s + i;
  }
}
// </vc-code>