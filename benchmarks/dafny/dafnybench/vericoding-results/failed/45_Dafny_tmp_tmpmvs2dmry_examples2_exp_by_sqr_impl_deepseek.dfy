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
lemma exp_even(x: real, n: nat)
  requires x >= 0.0
  requires n % 2 == 0
  requires n > 0
  ensures exp(x * x, n / 2) == exp(x, n)
  decreases n
{
  if n == 2 {
    // Base case for n=2
    calc {
      exp(x * x, 2 / 2);
      ==
      exp(x * x, 1);
      ==
      (x * x) * exp(x * x, 0);
      ==
      (x * x) * 1.0;
      ==
      x * x;
      ==
      x * exp(x, 1);
      ==
      exp(x, 2);
    }
  } else {
    exp_even(x, n - 2);
    calc {
      exp(x * x, n / 2);
      == 
      (x * x) * exp(x * x, (n / 2) - 1);
      == { exp_even(x, n - 2); }
      (x * x) * exp(x, n - 2);
      == 
      x * (x * exp(x, n - 2));
      == 
      x * exp(x, n - 1);
      == 
      exp(x, n);
    }
  }
}

lemma exp_odd(x: real, n: nat)
  requires x >= 0.0
  requires n % 2 == 1
  requires n > 0
  ensures exp(x, n) == x * exp(x, n - 1)
  decreases n
{
  // This follows directly from the definition of exp
  calc {
    exp(x, n);
    ==
    x * exp(x, n - 1);
  }
}

lemma exp_zero_case(x: real, n: nat)
  requires x >= 0.0
  requires n == 0
  ensures exp(x, n) == 1.0
{
  // Trivial from exp definition
}
// </vc-helpers>

// <vc-spec>
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
// </vc-spec>
// <vc-code>
{
  r := 1.0;
  var x := x0;
  var n := n0;
  
  while n > 0
    invariant x >= 0.0
    invariant r * exp(x, n) == exp(x0, n0)
    decreases n
  {
    if n % 2 == 1 {
      // Odd case
      r := r * x;
      n := n - 1;
      assert r * exp(x, n) == exp(x0, n0) by {
        calc {
          r * exp(x, n);
          ==  // r = old(r) * x
          (old(r) * x) * exp(x, n);
          ==  // Associativity
          old(r) * (x * exp(x, n));
          ==  // Definition of exp: x * exp(x, n) = exp(x, n + 1)
          old(r) * exp(x, n + 1);
          ==  // n + 1 = old(n)
          old(r) * exp(x, old(n));
          ==  // Loop invariant before update
          exp(x0, n0);
        }
      }
    } else {
      // Even case
      x := x * x;
      n := n / 2;
      assert r * exp(x, n) == exp(x0, n0) by {
        calc {
          r * exp(x, n);
          ==  // x = old(x) * old(x), n = old(n) / 2
          r * exp(old(x) * old(x), old(n) / 2);
          ==  { exp_even(old(x), old(n)); }
          r * exp(old(x), old(n));
          ==  // Loop invariant before update
          exp(x0, n0);
        }
      }
    }
  }
}
// </vc-code>

