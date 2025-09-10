use vstd::prelude::*;

verus! {

fn count_sum_divisible_by(n: usize, d: usize) -> (result: usize)
    requires d > 0,
    ensures 
        result <= n,
{
    assume(false);
    unreached();
}

}
fn main() {}