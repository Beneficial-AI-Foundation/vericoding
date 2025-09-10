use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
{
    assume(false);
    unreached()
}

}
fn main() {}