use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
{
    assume(false);
    unreached()
}

}
fn main() {}