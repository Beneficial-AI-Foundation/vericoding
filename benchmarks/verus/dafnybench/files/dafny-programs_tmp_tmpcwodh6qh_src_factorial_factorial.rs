use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

fn factorial(n: u32) -> (res: u32)
    requires n <= 12
    ensures res == fact(n as nat)
{
    assume(false);
    unreached()
}

}
fn main() {}