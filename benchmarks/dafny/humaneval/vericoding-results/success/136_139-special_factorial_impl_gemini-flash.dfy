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
lemma special_factorial_rec_unfold(n: nat)
    requires n > 0
    ensures special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1) {}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)

  requires n > 0

  ensures result == special_factorial_rec(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 1;
  }

  var res := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant res == special_factorial_rec(i - 1)
  {
    res := res * factorial(i);
    i := i + 1;
  }
  return res;
}
// </vc-code>
