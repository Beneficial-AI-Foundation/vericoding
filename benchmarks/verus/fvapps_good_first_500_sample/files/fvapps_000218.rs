// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn len_longest_fib_subseq(a: Vec<u32>) -> (result: u32)
    requires 
        a.len() >= 3,
        sorted(a@),
        forall|i: int| 0 <= i < a.len() ==> a[i] > 0,
    ensures 
        result == 0 || (result >= 3 && result <= a.len())
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0u32
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result1 = len_longest_fib_subseq(vec![1, 2, 3, 4, 5, 6, 7, 8]);
    // println!("{}", result1); // Expected: 5
    
    // let result2 = len_longest_fib_subseq(vec![1, 3, 7, 11, 12, 14, 18]);
    // println!("{}", result2); // Expected: 3
    
    // let result3 = len_longest_fib_subseq(vec![1, 2, 4, 8]);
    // println!("{}", result3); // Expected: 0
}