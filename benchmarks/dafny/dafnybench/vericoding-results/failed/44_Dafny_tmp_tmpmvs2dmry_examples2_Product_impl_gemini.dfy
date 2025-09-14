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
/* helper modified by LLM (iteration 5): no helpers needed for iterative solution */
// </vc-helpers>

// <vc-spec>
method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using an upward-counting loop */
{
  res := 0;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant res == m * i
  {
    res := res + m;
    i := i + 1;
  }
}
// </vc-code>
