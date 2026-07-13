// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_equal_tuples(n: usize, arr: Vec<i32>) -> (result: usize)
    requires 
        n >= 4,
        arr.len() == n,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] >= 1 && arr[i] <= n,
    ensures 
        result >= 0,
        (forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> #[trigger] arr[i] != #[trigger] arr[j]) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview */
/* Assurance level: unguarded */

}
fn main() {
    // #eval count_equal_tuples 5 [2, 2, 2, 2, 2]
    // #eval count_equal_tuples 6 [1, 3, 3, 1, 2, 3]  
    // #eval count_equal_tuples 4 [1, 1, 1, 1]
}