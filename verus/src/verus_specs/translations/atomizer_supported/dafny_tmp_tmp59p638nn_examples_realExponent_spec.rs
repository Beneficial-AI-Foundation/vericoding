// ATOM 

spec fn power(n: real, alpha: real) -> real
    recommends n > 0.0 && alpha > 0.0
{
    unimplemented!()
}

// ATOM 

spec fn log(n: real, alpha: real) -> real
    recommends n > 0.0 && alpha > 0.0
{
    unimplemented!()
}

// ATOM 

proof fn consistency(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures log(power(n,alpha), alpha) == n
    ensures power(log(n, alpha), alpha) == n
{
}

// ATOM 

proof fn logarithmSum(n: real, alpha: real, x: real, y: real)
    requires n > 0.0 && alpha > 0.0
    requires x > 0.0
    requires n == x * y
    ensures log(n,alpha) == log(x, alpha) +  log(y, alpha)
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

// ATOM 

proof fn test() {
    let pow3 = power(3.0,4.0);
    consistency(3.0,4.0);
    let log6 = log(6.0,8.0);
    logarithmSum(6.0, 8.0, 2.0, 3.0);
}

// ATOM 

proof fn test2() {
    let pow3 = power(3.0, 4.0);
    let power4 = power(4.0, 4.0);
    powerLemma(3.0, 4.0);
}

// SPEC 

pub fn pow(n: nat, alpha: real) -> real
    requires n > 0
    requires alpha > 0.0
    ensures power(n as real, alpha) == result
{
}