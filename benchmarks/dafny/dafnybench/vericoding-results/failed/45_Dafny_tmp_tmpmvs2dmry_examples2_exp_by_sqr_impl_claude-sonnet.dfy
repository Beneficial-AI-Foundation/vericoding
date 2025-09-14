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
lemma exp_by_sqr_lemma(x: real, n: nat)
requires x >= 0.0
ensures n % 2 == 0 ==> exp(x, n) == exp(x * x, n / 2)
ensures n % 2 == 1 ==> exp(x, n) == x * exp(x * x, n / 2)
decreases n
{
    if n == 0 {
        assert exp(x, 0) == 1.0;
        assert exp(x * x, 0) == 1.0;
    } else if n == 1 {
        assert exp(x, 1) == x * exp(x, 0) == x * 1.0 == x;
        assert x * exp(x * x, 0) == x * 1.0 == x;
    } else if n % 2 == 0 {
        var half := n / 2;
        assert n == 2 * half;
        exp_by_sqr_lemma(x, 2 * half - 1);
        exp_by_sqr_lemma(x, 2 * half - 2);
        assert exp(x, n) == exp(x, 2 * half);
        calc {
            exp(x, 2 * half);
            == x * exp(x, 2 * half - 1);
            == x * x * exp(x, 2 * half - 2);
        }
        exp_by_sqr_lemma(x * x, half - 1);
    } else {
        var half := n / 2;
        assert n == 2 * half + 1;
        exp_by_sqr_lemma(x, 2 * half);
        calc {
            exp(x, n);
            == exp(x, 2 * half + 1);
            == x * exp(x, 2 * half);
        }
        exp_by_sqr_lemma(x * x, half);
    }
}

lemma exp_odd_case(x: real, n: nat)
requires x >= 0.0 && n % 2 == 1
ensures exp(x, n) == x * exp(x, n - 1)
{
    if n > 0 {
        assert exp(x, n) == x * exp(x, n - 1);
    }
}

lemma exp_even_case(x: real, n: nat)
requires x >= 0.0 && n % 2 == 0 && n > 0
ensures exp(x, n) == exp(x * x, n / 2)
{
    exp_by_sqr_lemma(x, n);
}
// </vc-helpers>

// <vc-spec>
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
// </vc-spec>
// <vc-code>
{
    var x := x0;
    var n := n0;
    r := 1.0;
    
    while n > 0
    invariant x >= 0.0
    invariant r * exp(x, n) == exp(x0, n0)
    decreases n
    {
        if n % 2 == 1 {
            exp_odd_case(x, n);
            r := r * x;
            n := n - 1;
        } else {
            exp_even_case(x, n);
            x := x * x;
            n := n / 2;
        }
    }
}
// </vc-code>

