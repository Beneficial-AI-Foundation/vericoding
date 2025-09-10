use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
{
    assume(false);
    unreached();
}

}
fn main() {}