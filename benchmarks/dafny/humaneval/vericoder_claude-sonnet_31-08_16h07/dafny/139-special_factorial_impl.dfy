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
lemma special_factorial_rec_step(n: nat)
  requires n > 0
  ensures special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1)
{
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
  if n == 1 {
    result := 1;
  } else {
    var prev := special_factorial(n - 1);
    var fact_n := 1;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant fact_n == factorial(i - 1)
    {
      fact_n := fact_n * i;
      i := i + 1;
    }
    result := fact_n * prev;
  }
}
// </vc-code>

