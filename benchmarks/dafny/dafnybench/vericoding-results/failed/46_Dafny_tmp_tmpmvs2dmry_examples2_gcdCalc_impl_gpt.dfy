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
lemma gcdMinusLeft(a: nat, b: nat)
  requires a > 0 && b > 0 && a > b
  ensures gcd(a, b) == gcd(a - b, b)
{
  reveal gcd();
  assert gcd(a, b) == gcd(a - b, b);
}

lemma gcdMinusRight(a: nat, b: nat)
  requires a > 0 && b > 0 && b > a
  ensures gcd(a, b) == gcd(a, b - a)
{
  reveal gcd();
  assert gcd(a, b) == gcd(a, b - a);
}

lemma gcd_eq_same(x: nat)
  requires x > 0
  ensures gcd(x, x) == x
{
  reveal gcd();
  assert gcd(x, x) == x;
}
// </vc-helpers>

// <vc-spec>
method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
// </vc-spec>
// <vc-code>
{
  var a := m;
  var b := n;
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      ghost var oa := a;
      gcdMinusLeft(oa, b);
      a := a - b;
      assert a == oa - b;
      assert gcd(oa, b) == gcd(a, b);
    } else {
      ghost var ob := b;
      gcdMinusRight(a, ob);
      b := b - a;
      assert b == ob - a;
      assert gcd(a, ob) == gcd(a, b);
    }
  }
  assert a == b;
  gcd_eq_same(a);
  assert gcd(a, b) == a;
  assert gcd(a, b) == gcd(m, n);
  res := a;
}
// </vc-code>

