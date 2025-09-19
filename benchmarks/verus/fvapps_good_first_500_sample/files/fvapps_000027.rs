// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_trailing_zeros(n: u32) -> u32 
    decreases n
{
    if n % 2 == 1 {
        0u32
    } else {
        1u32 + count_trailing_zeros(n / 2)
    }
}

fn min_moves_to_odd(arrays: Vec<Vec<u32>>) -> (result: Vec<u32>)
    ensures 
        result.len() == arrays.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}

fn count_trailing_zeros_fn(n: u32) -> (result: u32)
    ensures result == count_trailing_zeros(n)
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // let test1 = vec![vec![40, 6, 40, 3, 20, 1]];
    // let result1 = min_moves_to_odd(test1);
    // assert_eq!(result1, vec![4]);

    // let test2 = vec![vec![1024]];
    // let result2 = min_moves_to_odd(test2);
    // assert_eq!(result2, vec![10]);

    // let test3 = vec![vec![2, 4, 8, 16]];
    // let result3 = min_moves_to_odd(test3);
    // assert_eq!(result3, vec![4]);

    // let test4 = vec![vec![3, 1, 7]];
    // let result4 = min_moves_to_odd(test4);
    // assert_eq!(result4, vec![0]);
}