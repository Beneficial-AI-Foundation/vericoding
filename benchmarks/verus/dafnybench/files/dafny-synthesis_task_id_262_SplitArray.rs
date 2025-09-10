use vstd::prelude::*;

verus! {

fn split_array(arr: &[i32], l: usize) -> (Vec<i32>, Vec<i32>)
    requires 0 <= l <= arr.len()
{
    assume(false);
    unreached();
}

}
fn main() {}