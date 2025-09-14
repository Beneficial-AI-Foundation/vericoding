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
function power(x: real, n: nat) :real
decreases n
{
    if n == 0 then 1.0
    else if x == 0.0 then 0.0
    else x * power(x, n - 1)
}
lemma ExpBySqrProperty(x: real, n: nat)
    requires x >= 0.0
    ensures exp(x, n) == (if n == 0 then 1.0 else if x == 0.0 then 0.0 else if n % 2 == 0 then exp(x, n / 2) * exp(x, n / 2) else x * exp(x, n / 2) * exp(x, n / 2))
{
    if n == 0 {
    } else if x == 0.0 {
    } else if n % 2 == 0 {
        calc {
            exp(x, n);
            exp(x, n-1) * x;
            {assert n > 0;} // n is even and > 0, so n-1 is odd
            {assert n/2 + n/2 == n;}
            exp(x, n / 2) * exp(x, n / 2);
        }
    } else {
        calc {
            exp(x, n);
            x * exp(x, n - 1);
            {assert n > 0;} // n is odd and > 0, so n-1 is even
            {assert (n-1)/2 + (n-1)/2 == n-1;}
            {assert (n / 2) == (n-1)/2;} // Integer division
            x * exp(x, n / 2) * exp(x, n / 2);
        }
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
    if n0 == 0 {
        return 1.0;
    } else if x0 == 0.0 {
        return 0.0;
    } else {
        ExpBySqrProperty(x0, n0); // Prove the property related to exp function
        if n0 % 2 == 0 {
            var temp_r := exp_by_sqr(x0, n0 / 2);
            return temp_r * temp_r;
        } else {
            var temp_r := exp_by_sqr(x0, n0 / 2);
            return x0 * temp_r * temp_r;
        }
    }
}
// </vc-code>

