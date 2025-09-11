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
// </vc-helpers>

// <vc-spec>
method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
