// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

spec fn max_abs_val_expr_value(arr1: Seq<i32>, arr2: Seq<i32>, i: int, j: int) -> int {
    if 0 <= i < arr1.len() && 0 <= j < arr1.len() && arr1.len() == arr2.len() {
        abs_diff(arr1[i] as int, arr1[j] as int) + abs_diff(arr2[i] as int, arr2[j] as int) + abs_diff(i, j)
    } else {
        0
    }
}

fn max_abs_val_expr(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: i32)
    requires 
        arr1.len() == arr2.len(),
        arr1.len() >= 2,
        forall|i: int| 0 <= i < arr1.len() ==> #[trigger] arr1[i] >= -1000000 && #[trigger] arr1[i] <= 1000000,
        forall|i: int| 0 <= i < arr2.len() ==> #[trigger] arr2[i] >= -1000000 && #[trigger] arr2[i] <= 1000000,
    ensures 
        result >= 0,
        exists|i: int, j: int| 0 <= i < arr1.len() && 0 <= j < arr1.len() && 
            result as int == max_abs_val_expr_value(arr1@, arr2@, i, j),
        forall|i: int, j: int| 0 <= i < arr1.len() && 0 <= j < arr1.len() ==> 
            result as int >= max_abs_val_expr_value(arr1@, arr2@, i, j),
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
    // let result1 = max_abs_val_expr(vec![1, 2, 3, 4], vec![-1, 4, 5, 6]);
    // println!("Result 1: {}", result1); // Expected: 13
    
    // let result2 = max_abs_val_expr(vec![1, -2, -5, 0, 10], vec![0, -2, -1, -7, -4]);
    // println!("Result 2: {}", result2); // Expected: 20
    
    // let result3 = max_abs_val_expr(vec![1, 1], vec![1, 1]);
    // println!("Result 3: {}", result3); // Expected: 1
}