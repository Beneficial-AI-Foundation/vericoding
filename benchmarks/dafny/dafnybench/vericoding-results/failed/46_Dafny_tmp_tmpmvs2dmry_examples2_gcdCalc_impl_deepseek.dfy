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
lemma GcdLemma(a: nat, b: nat, res: nat)
  requires a > 0 && b > 0
  requires res == gcd(if a > b then a - b else a, if b > a then b - a else b)
  ensures res == gcd(a, b)
{
  if a == b {
    assert gcd(a, b) == a;
  } else if a > b {
    assert gcd(a, b) == gcd(a - b, b);
  } else {
    assert gcd(a, b) == gcd(a, b - a);
  }
}

lemma GcdSubtraction(a: nat, b: nat)
  requires a > 0 && b > 0
  ensures a > b ==> m := a - b
    ensures m > 0 && gcd(m, b) == gcd(a, b)
{
  if a > b {
    var m := a - b;
    assert gcd(a, b) == gcd(m, b);
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
  if m == n {
    res := n;
  } else if m > n {
    var m' := m - n;
    assert m' > 0;
    var subRes := gcdCalc(m', n);
    res := subRes;
    GcdLemma(m, n, res);
  } else {
    var n' := n - m;
    assert n' > 0;
    var subRes := gcdCalc(m, n');
    res := subRes;
    GcdLemma(m, n, res);
  }
}
// </vc-code>

