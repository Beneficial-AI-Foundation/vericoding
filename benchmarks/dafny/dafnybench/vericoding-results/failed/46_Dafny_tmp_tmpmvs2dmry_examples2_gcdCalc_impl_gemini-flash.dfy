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

// method add_by_inc_vc(x: int, y:int) returns (z:int)
// {
//     assume x>=0 && y>=0;
//     z := x;
//     var i := 0;
//     assert 0 <= i <= y && z == x + i;
//     z,i = *,*;
//     assume 0 <= i <= y && z == x + i;
//     if (i < y) 
//     {
//         ghost var rank0 := y-i
//         z := z+1;
//         i := i+1; 
//         assert(y-i < rank0)
//         ghost var rank1 := y-i
//         assert(rank1 < rank0)
//         assert(rank1 >=0)
//         assert 0 <= i <= y && z == x + i;
//         assume(false);
//     }
//     assert (z == x+y);
//     assert (i == y);
//     return z;
// }

// <vc-helpers>
function private_gcd(m: nat, n: nat) : nat
requires m > 0 && n > 0
decreases m + n
{
    if m == n then n
    else if m > n then private_gcd(m - n, n)
    else private_gcd(m, n - m)
}
lemma lemma_gcd_equality(m: nat, n: nat)
  requires m > 0 && n > 0
  ensures gcd(m, n) == private_gcd(m, n)
{
  if m == n {
  } else if m > n {
    calc {
      gcd(m, n);
      gcd(m - n, n);
      { lemma_gcd_equality(m - n, n); }
      private_gcd(m - n, n);
      private_gcd(m, n);
    }
  } else {
    calc {
      gcd(m, n);
      gcd(m, n - m);
      { lemma_gcd_equality(m, n - m); }
      private_gcd(m, n - m);
      private_gcd(m, n);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
// </vc-spec>
// <vc-code>
{
  var M := m;
  var N := n;
  lemma_gcd_equality(m, n);
  while M != N
    invariant M > 0 && N > 0
    invariant private_gcd(M, N) == private_gcd(m, n)
    decreases M + N
  {
    if M > N {
      M := M - N;
    } else {
      N := N - M;
    }
  }
  res := M;
  lemma_gcd_equality(M, N); // To show that M (which is N) is the gcd(m,n)
}
// </vc-code>

