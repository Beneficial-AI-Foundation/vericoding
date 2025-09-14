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
lemma exp_succ(x: real, n: nat) ensures exp(x, n+1) == x * exp(x, n)
decreases n
{
  // Unfold definition of exp at n+1
  assert exp(x, n+1) == x * exp(x, n);
}

lemma exp_add(x: real, m: nat, n: nat) ensures exp(x, m + n) == exp(x,m) * exp(x,n)
decreases n
{
  if n == 0 {
    // exp(x, m+0) == exp(x,m) and exp(x,0) == 1.0
    assert exp(x, m + 0) == exp(x, m);
    assert exp(x, 0) == 1.0;
    assert exp(x, m) == exp(x,m) * exp(x,0);
  } else {
    exp_add(x, m, n-1);
    // Use successor form for exp on the second factor and for the sum
    exp_succ(x, n-1);
    exp_succ(x, m+n-1);
    // From IH: exp(x, m + n - 1) == exp(x,m) * exp(x,n-1)
    assert exp(x, m + n - 1) == exp(x,m) * exp(x,n-1);
    // Combine to get exp(x, m + n) == exp(x,m) * exp(x,n)
    assert exp(x, m + n) == x * exp(x, m + n - 1);
    assert x * exp(x, m + n - 1) == x * (exp(x,m) * exp(x,n-1));
    assert x * (exp(x,m) * exp(x,n-1)) == exp(x,m) * (x * exp(x,n-1));
    assert x * exp(x,n-1) == exp(x,n);
    assert exp(x,m) * (x * exp(x,n-1)) == exp(x,m) * exp(x,n);
  }
}

lemma exp_mul_arg(x: real, y: real, k: nat) ensures exp(x*y, k) == exp(x,k) * exp(y,k)
decreases k
{
  if k == 0 {
    // both sides are 1.0
    assert exp(x*y, 0) == 1.0;
    assert exp(x, 0) == 1.0;
    assert exp(y, 0) == 1.0;
    assert exp(x*y, 0) == exp(x,0) * exp(y,0);
  } else {
    exp_mul_arg(x, y, k-1);
    exp_succ(x*y, k-1);
    exp_succ(x, k-1);
    exp_succ(y, k-1);
    // From successor forms:
    assert exp(x,k) == x * exp(x,k-1);
    assert exp(y,k) == y * exp(y,k-1);
    // Combine both succ forms directly
    assert exp(x,k) * exp(y,k) == (x * exp(x,k-1)) * (y * exp(y,k-1));
    // Rearrange multiplications to factor (x*y)
    assert (x * exp(x,k-1)) * (y * exp(y,k-1)) == (x*y) * (exp(x,k-1) * exp(y,k-1));
    // Use IH for k-1
    assert exp(x*y,k-1) == exp(x,k-1) * exp(y,k-1);
    assert (x*y) * (exp(x,k-1) * exp(y,k-1)) == (x*y) * exp(x*y,k-1);
    assert exp(x*y, k) == (x*y) * exp(x*y, k-1);
    assert exp(x*y, k) == exp(x,k) * exp(y,k);
  }
}
// </vc-helpers>

// <vc-spec>
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
// </vc-spec>
// <vc-code>
{
  var a := x0;
  var m := n0;
  var acc := 1.0;
  while m > 0
    invariant acc * exp(a, m) == exp(x0, n0)
    decreases m
  {
    if m % 2 == 1 {
      // m is odd: exp(a,m) = a * exp(a,m-1)
      exp_succ(a, m-1);
      // update accumulator and exponent
      acc := acc * a;
      m := m - 1;
      // invariant holds after update
      assert acc * exp(a, m) == exp(x0, n0);
    } else {
      var k := m / 2;
      // ensure m is even and relate m and k
      assert m % 2 == 0;
      assert m == k + k;
      // use lemmas to show exp(a,m) == exp(a*a,k)
      exp_add(a, k, k);
      exp_mul_arg(a, a, k);
      assert exp(a, m) == exp(a*a, k);
      // square base and halve exponent
      a := a * a;
      m := k;
      // invariant holds after update
      assert acc * exp(a, m) == exp(x0, n0);
    }
  }
  r := acc;
}
// </vc-code>

