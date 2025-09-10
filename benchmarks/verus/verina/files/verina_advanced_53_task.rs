use vstd::prelude::*;

verus! {

fn minimum_right_shifts(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() <= i32::MAX,
        forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] != nums[j],
    ensures
        ({
            let n = nums.len() as i32;
            if n <= 1 {
                result == 0
            } else {
                (result >= 0 && result < n) || result == -1
            }
        }),
{
    assume(false);
    unreached()
}

}
fn main() {}