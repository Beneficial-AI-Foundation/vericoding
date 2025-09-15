// <vc-preamble>
function factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}
function special_factorial_rec(n: nat): nat
  decreases n
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)

  requires n > 0

  ensures result == special_factorial_rec(n)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  result := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == special_factorial_rec(i - 1)
  {
    result := result * factorial(i);
    i := i + 1;
  }
}
// </vc-code>
