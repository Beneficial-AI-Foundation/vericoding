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
lemma gcd_sub_left(m: nat, n: nat)
  requires m > n && n > 0
  ensures gcd(m, n) == gcd(m - n, n)
  decreases m + n
{
  // By the definition of gcd (structural recursion by subtraction),
  // when m > n, gcd(m, n) equals gcd(m-n, n).
  assert gcd(m, n) == gcd(m - n, n);
}

lemma gcd_sub_right(m: nat, n: nat)
  requires n > m && m > 0
  ensures gcd(m, n) == gcd(m, n - m)
  decreases m + n
{
  // By the definition of gcd, when n > m, gcd(m, n) equals gcd(m, n-m).
  assert gcd(m, n) == gcd(m, n - m);
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
      ghost var oldA := a;
      ghost var oldB := b;
      // oldA > oldB and oldB > 0 hold due to the branch condition and invariant
      gcd_sub_left(oldA, oldB);
      a := oldA - oldB;
      // re-establish invariants
      assert a > 0;
      // from lemma: gcd(oldA,oldB) == gcd(oldA-oldB, oldB), and invariant: gcd(oldA,oldB) == gcd(m,n)
      assert gcd(a, b) == gcd(m, n);
    } else {
      ghost var oldA := a;
      ghost var oldB := b;
      // oldB > oldA and oldA > 0 hold due to the branch condition and invariant
      gcd_sub_right(oldA, oldB);
      b := oldB - oldA;
      // re-establish invariants
      assert b > 0;
      // from lemma and invariant
      assert gcd(a, b) == gcd(m, n);
    }
  }
  res := a;
}
// </vc-code>

