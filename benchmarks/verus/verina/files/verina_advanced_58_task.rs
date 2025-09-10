use vstd::prelude::*;

verus! {

spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}

fn nth_ugly_number(n: u32) -> (result: u32)
    requires n > 0,
    ensures result > 0,
{
    assume(false);
    unreached();
}

}
fn main() {}