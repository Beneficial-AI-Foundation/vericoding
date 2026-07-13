// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_divisible_before(arr: Seq<nat>, i: int) -> nat
    decreases i
{
    if i <= 0 || arr.len() == 0 {
        0
    } else {
        let idx = i - 1;
        let current_count: nat = if idx >= 0 && idx < arr.len() && i < arr.len() && arr[idx] % arr[i] == 0 { 1 } else { 0 };
        current_count + count_divisible_before(arr, i - 1)
    }
}

spec fn star_value(arr: Seq<nat>, i: int) -> nat {
    if i >= arr.len() || i < 0 {
        0
    } else {
        count_divisible_before(arr, i)
    }
}

spec fn max_star_value_spec(arr: Seq<nat>) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else if arr.len() == 1 {
        0
    } else {
        let current_star = star_value(arr, arr.len() - 1);
        let rest_max = max_star_value_spec(arr.drop_last());
        if current_star > rest_max { current_star } else { rest_max }
    }
}

fn find_max_star_value(arr: Vec<nat>) -> (result: nat)
    ensures result == max_star_value_spec(arr@)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn count_divisible(arr: Vec<nat>, i: usize) -> (result: nat)
    requires i < arr.len(),
    ensures result == count_divisible_before(arr@, i as int)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
/* placeholder for additional code */
// </vc-code>


}

fn main() {
    // let test_arr = vec![8, 1, 28, 4, 2, 6, 7];
    // let result = find_max_star_value(test_arr);
    // println!("Result: {}", result);
}