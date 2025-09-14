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
method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Resubmitting correct iterative solution; previous failure was due to compilation warnings in uneditable preamble code, not a verification error in this implementation. */
  var a := m;
  var b := n;
  while (a != b)
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  res := a;
}
// </vc-code>
