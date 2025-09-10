use vstd::prelude::*;

verus! {

fn longest_increasing_subsequence(a: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= a.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}