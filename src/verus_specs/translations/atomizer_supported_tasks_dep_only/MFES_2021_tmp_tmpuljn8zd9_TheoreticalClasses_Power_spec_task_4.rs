use vstd::prelude::*;

verus! {

spec fn power(x: real, n: nat) -> real {
    if n == 0 { 1.0 } else { x * power(x, (n - 1) as nat) }
}

pub fn powerOpt(x: real, n: nat) -> (p: real)
    ensures p == power(x, n)
{
}

proof fn distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a + b)
{
}

pub fn testPowerOpt()
{
}

}