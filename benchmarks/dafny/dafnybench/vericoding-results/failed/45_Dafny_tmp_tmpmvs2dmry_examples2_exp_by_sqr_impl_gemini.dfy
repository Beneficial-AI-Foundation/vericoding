// <vc-preamble>
function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
decreases m+n
{
    if(m==n) then n 
    else if( m > n) then gcd(m-n,n)
    else gcd(m, n-m)
}

function exp(x: real, n: nat) :real
decreases n;
{
    if(n == 0) then 1.0
    else if (x==0.0) then 0.0
    else if (n  ==0 && x == 0.0) then 1.0
    else x*exp(x, n-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added a recursive proof for ExpEven */
lemma ExpEven(x: real, n: nat)
  requires x >= 0.0
  requires n > 0 && n % 2 == 0
  ensures exp(x * x, n / 2) == exp(x, n)
  decreases n
{
  if n > 2 {
    ExpEven(x, n-2);
  }
}
// </vc-helpers>

// <vc-spec>
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added call to helper with requires */
{
  var res := 1.0;
  var base := x0;
  var exp_n := n0;
  while exp_n > 0
    invariant exp_n >= 0
    invariant base >= 0.0
    invariant res * exp(base, exp_n) == exp(x0, n0)
    decreases exp_n
  {
    if exp_n % 2 == 0 {
      ExpEven(base, exp_n);
      base := base * base;
      exp_n := exp_n / 2;
    } else {
      res := res * base;
      exp_n := exp_n - 1;
    }
  }
  r := res;
}
// </vc-code>
