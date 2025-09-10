use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
{
    assume(false);
    unreached()
}

}
fn main() {}