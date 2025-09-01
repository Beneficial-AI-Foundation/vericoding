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
lemma lemma_special_factorial_rec(n: nat)
  requires n > 0
  ensures special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1)
{
  if n == 0 {
  } else {
    calc {
      special_factorial_rec(n);
      factorial(n) * special_factorial_rec(n - 1);
    }
  }
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
    var i := 1;
    result := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result == special_factorial_rec(i - 1)
    {
        result := result * factorial(i);
        i := i + 1;
    }
    assert special_factorial_rec(n) == result;
}
// </vc-code>

