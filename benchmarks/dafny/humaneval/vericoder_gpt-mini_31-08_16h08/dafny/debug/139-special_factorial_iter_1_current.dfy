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

// <vc-helpers>
lemma special_factorial_rec_step(i: nat)
  requires i > 0
  ensures special_factorial_rec(i) == factorial(i) * special_factorial_rec(i - 1)
{
  // By definition of special_factorial_rec on i>0
  assert special_factorial_rec(i) == factorial(i) * special_factorial_rec(i - 1);
}
// </vc-helpers>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == special_factorial_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i: nat := 1;
  var res: nat := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant res == special_factorial_rec(i - 1)
    decreases n + 1 - i
  {
    // update preserves invariant using the definition of special_factorial_rec
    res := res * factorial(i);
    i := i + 1;
  }
  result := res;
}
// </vc-code>

