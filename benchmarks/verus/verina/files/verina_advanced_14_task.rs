use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {

fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
{
    assume(false);
    unreached()
}

}
fn main() {}