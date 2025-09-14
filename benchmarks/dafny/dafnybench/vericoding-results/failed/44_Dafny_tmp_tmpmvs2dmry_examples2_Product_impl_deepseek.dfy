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
lemma ProductLemma(m: nat, n: nat, i: nat, acc: nat)
  requires i <= n
  ensures acc + m*(n - i) == m*n
  decreases n - i
{
  if i < n {
    calc {
      acc + m*(n - i);
      ==
      acc + m*((n - i) - 1 + 1);
      ==
      acc + m + m*((n - i) - 1);
      ==
      (acc + m) + m*((n - (i + 1)));
      == { ProductLemma(m, n, i + 1, acc + m); }
      m*n;
    }
  }
}

lemma ZeroMultiplication(m: nat)
  ensures m * 0 == 0
{
}

lemma MultiplyByZero(m: nat)
  ensures 0 * m == 0
{
}
// </vc-helpers>

// <vc-spec>
method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
// </vc-spec>
// <vc-code>
{
  res := 0;
  var i : nat := 0;
  while i < n
    invariant i <= n
    invariant res == m * i
  {
    res := res + m;
    i := i + 1;
  }
  if n == 0 {
    assert m * 0 == 0 by { ZeroMultiplication(m); }
    assert 0 * m == 0 by { MultiplyByZero(m); }
  }
  assert res == m * n by {
    if n > 0 {
      ProductLemma(m, n, i, res);
    }
  }
  return res;
}
// </vc-code>

