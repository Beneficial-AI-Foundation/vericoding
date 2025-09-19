// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn MOD() -> int { 1000000007 }

spec fn list_sum(arr: Seq<i32>) -> int
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        arr[0] as int + list_sum(arr.skip(1))
    }
}

fn k_concatenation_max_sum(arr: Vec<i32>, k: usize) -> (result: i32)
    requires 
        k > 0,
        arr.len() >= 1,
    ensures 
        result >= 0,
        result < MOD(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

}

fn main() {
    // println!("{}", k_concatenation_max_sum(vec![1, 2], 3));
    // println!("{}", k_concatenation_max_sum(vec![1, -2, 1], 5));
    // println!("{}", k_concatenation_max_sum(vec![-1, -2], 7));
}