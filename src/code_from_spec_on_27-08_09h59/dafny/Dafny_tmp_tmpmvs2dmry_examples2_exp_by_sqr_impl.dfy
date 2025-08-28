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
lemma exp_mult_property(x: real, a: nat, b: nat)
    ensures exp(x, a + b) == exp(x, a) * exp(x, b)
{
    if a == 0 {
        assert exp(x, a + b) == exp(x, b);
        assert exp(x, a) == 1.0;
    } else {
        exp_mult_property(x, a - 1, b);
        assert exp(x, (a - 1) + b) == exp(x, a - 1) * exp(x, b);
        assert exp(x, a + b) == x * exp(x, (a - 1) + b);
        assert exp(x, a) == x * exp(x, a - 1);
    }
}

lemma exp_square_property(x: real, n: nat)
    ensures exp(x, 2 * n) == exp(x * x, n)
{
    if n == 0 {
        assert exp(x, 2 * n) == exp(x, 0) == 1.0;
        assert exp(x * x, n) == exp(x * x, 0) == 1.0;
    } else {
        exp_square_property(x, n - 1);
        assert exp(x, 2 * (n - 1)) == exp(x * x, n - 1);
        exp_mult_property(x, 2, 2 * (n - 1));
        assert exp(x, 2 + 2 * (n - 1)) == exp(x, 2) * exp(x, 2 * (n - 1));
        assert exp(x, 2) == x * x;
        assert exp(x, 2 * n) == (x * x) * exp(x * x, n - 1);
        assert exp(x * x, n) == (x * x) * exp(x * x, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n0 == 0 {
        r := 1.0;
    } else if x0 == 0.0 {
        r := 0.0;
    } else {
        var x := x0;
        var n := n0;
        r := 1.0;
        
        while n > 0
            invariant x >= 0.0
            invariant r * exp(x, n) == exp(x0, n0)
            decreases n
        {
            if n % 2 == 1 {
                r := r * x;
                n := n - 1;
                exp_mult_property(x, 1, n);
            } else {
                exp_square_property(x, n / 2);
                x := x * x;
                n := n / 2;
            }
        }
    }
}
// </vc-code>
