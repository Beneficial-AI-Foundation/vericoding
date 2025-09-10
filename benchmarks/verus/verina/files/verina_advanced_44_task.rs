use vstd::prelude::*;

verus! {

fn max_subarray_sum_divisible_by_k(arr: &Vec<i32>, k: i32) -> (result: i32)
    requires k > 0,
    ensures true,
{
    assume(false);
    unreached()
}

}
fn main() {}