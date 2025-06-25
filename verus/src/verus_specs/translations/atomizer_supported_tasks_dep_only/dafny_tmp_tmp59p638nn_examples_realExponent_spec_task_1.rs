// ATOM 

spec fn power(n: real, alpha: real) -> real
    recommends n > 0.0 && alpha > 0.0
{
    unimplemented!()
}

proof fn power_ensures(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
{
}

// ATOM 

proof fn powerLemma(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) * alpha == power(n+1.0, alpha)
{
}

// ATOM 

proof fn power1(alpha: real)
    requires alpha > 0.0
    ensures power(1.0, alpha) == alpha
{
}

// SPEC 

pub fn pow(n: nat, alpha: real) -> (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
{
}