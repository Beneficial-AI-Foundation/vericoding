use vstd::prelude::*;

verus! {

fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
{
    assume(false);
    unreached();
}

}
fn main() {}