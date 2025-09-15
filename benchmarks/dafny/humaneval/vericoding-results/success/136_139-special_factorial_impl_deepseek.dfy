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
function special_factorial_rec_helper(n: nat): (r: nat)
  decreases n
  ensures r == special_factorial_rec(n)
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec_helper(n - 1)
}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)

  requires n > 0

  ensures result == special_factorial_rec(n)
// </vc-spec>
// <vc-code>
{
  var current := 1;
  result := 1;
  
  while current <= n
    invariant 1 <= current <= n + 1
    invariant result == special_factorial_rec(current - 1)
  {
    result := result * factorial(current);
    current := current + 1;
  }
}
// </vc-code>
