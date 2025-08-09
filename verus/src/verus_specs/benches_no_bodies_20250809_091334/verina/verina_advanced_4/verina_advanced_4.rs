use vstd::prelude::*;

verus! {

fn int_max(x: i32, y: i32) -> (result: i32)
    ensures result >= x && result >= y
{
    return 0;  // TODO: Remove this line and implement the function body
}

spec fn longest_increasing_subsequence_precond(a: Seq<i32>) -> bool {
    true
}

spec fn longest_increasing_subsequence_postcond(a: Seq<i32>, result: i32) -> bool {
    result >= 0
}

fn longest_increasing_subsequence(a: Vec<i32>) -> (result: i32)
    requires longest_increasing_subsequence_precond(a@)
    ensures longest_increasing_subsequence_postcond(a@, result)
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!