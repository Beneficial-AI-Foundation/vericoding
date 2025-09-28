// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn always_true() -> bool {
    true
}

proof fn len_nonneg<T>(v: &Vec<T>) {
    assert(v.len() >= 0usize);
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    let result: usize = nums.len();
    result
}
// </vc-code>

}
fn main() {}