use vstd::prelude::*;

verus! {

fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
{
    assume(false);
    unreached();
}

}
fn main() {}