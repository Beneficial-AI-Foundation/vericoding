use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13,
    ensures result == factorial(n as nat)
{
    assume(false);
    unreached()
}

}
fn main() {}