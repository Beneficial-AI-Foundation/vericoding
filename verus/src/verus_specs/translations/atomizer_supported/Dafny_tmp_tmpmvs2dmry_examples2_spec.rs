// SPEC 
pub fn add_by_inc(x: nat, y: nat) -> (z: nat)
    ensures(z == x + y)
{
}

// SPEC 
pub fn Product(m: nat, n: nat) -> (res: nat)
    ensures(res == m * n)
{
}

// SPEC 
pub fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires(m > 0 && n > 0)
    ensures(res == gcd(m, n))
{
}

// ATOM 
spec fn gcd(m: nat, n: nat) -> nat
    requires(m > 0 && n > 0)
{
    if m == n { 
        n 
    } else if m > n { 
        gcd(m - n, n)
    } else { 
        gcd(m, n - m)
    }
}

// SPEC 
pub fn exp_by_sqr(x0: real, n0: nat) -> (r: real)
    requires(x0 >= 0.0)
    ensures(r == exp(x0, n0))
{
}

// ATOM 
spec fn exp(x: real, n: nat) -> real
{
    if n == 0 { 
        1.0
    } else if x == 0.0 { 
        0.0
    } else if n == 0 && x == 0.0 { 
        1.0
    } else { 
        x * exp(x, n - 1)
    }
}