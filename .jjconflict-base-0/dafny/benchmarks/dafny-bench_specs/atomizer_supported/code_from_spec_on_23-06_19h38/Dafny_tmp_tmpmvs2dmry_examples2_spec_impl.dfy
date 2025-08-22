// IMPL add_by_inc
method add_by_inc(x: nat, y:nat) returns (z:nat)
ensures z == x+y;
{
    z := x;
    var i := 0;
    while i < y
        invariant 0 <= i <= y
        invariant z == x + i
    {
        z := z + 1;
        i := i + 1;
    }
}

// IMPL Product
method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
{
    res := 0;
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant res == i * n
    {
        /* code modified by LLM (iteration 4): call add_by_inc and assign return value */
        res := add_by_inc(res, n);
        i := i + 1;
    }
}

// IMPL gcdCalc
method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
{
    var a := m;
    var b := n;
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a, b) == gcd(m, n)
        /* code modified by LLM (iteration 4): add decreases clause for termination */
        decreases a + b
    {
        if a > b {
            a := a - b;
        } else {
            b := b - a;
        }
    }
    res := a;
}

// ATOM gcd
function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
{
    if(m==n) then n 
    else if( m > n) then gcd(m-n,n)
    else gcd(m, n-m)
}

// IMPL exp_by_sqr
method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
{
    if n0 == 0 {
        r := 1.0;
        return;
    }
    
    if x0 == 0.0 {
        r := 0.0;
        return;
    }
    
    r := 1.0;
    var base := x0;
    var n := n0;
    
    while n > 0
        /* code modified by LLM (iteration 4): corrected loop invariant */
        invariant r * exp(base, n) == exp(x0, n0)
        invariant base >= 0.0
        decreases n
    {
        if n % 2 == 1 {
            /* code modified by LLM (iteration 4): establish relationship before assignment */
            assert exp(base, n) == base * exp(base, n-1);
            r := r * base;
            n := n - 1;
        } else {
            /* code modified by LLM (iteration 4): use lemma and establish relationship */
            ExpSquareProperty(base, n / 2);
            assert exp(base, n) == exp(base * base, n / 2);
            base := base * base;
            n := n / 2;
        }
    }
}

/* code modified by LLM (iteration 4): added lemma for exponentiation square property */
lemma ExpSquareProperty(base: real, k: nat)
    ensures exp(base, 2 * k) == exp(base * base, k)
{
    if k == 0 {
        // Base case: exp(base, 0) == 1.0 == exp(base * base, 0)
    } else {
        // Inductive case
        ExpSquareProperty(base, k - 1);
        assert exp(base, 2 * (k - 1)) == exp(base * base, k - 1);
        assert exp(base, 2 * k) == exp(base, 2 * (k - 1) + 2);
        assert exp(base, 2 * (k - 1) + 2) == exp(base, 2 * (k - 1)) * base * base;
        assert exp(base, 2 * (k - 1)) * base * base == exp(base * base, k - 1) * (base * base);
        assert exp(base * base, k - 1) * (base * base) == exp(base * base, k);
    }
}

// ATOM exp
function exp(x: real, n: nat) :real
{
    if(n == 0) then 1.0
    else if (x==0.0) then 0.0
    else if (n  ==0 && x == 0.0) then 1.0
    else x*exp(x, n-1)
}