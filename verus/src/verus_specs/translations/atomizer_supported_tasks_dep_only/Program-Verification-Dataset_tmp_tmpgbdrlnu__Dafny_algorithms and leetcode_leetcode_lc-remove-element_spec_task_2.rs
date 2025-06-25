pub fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: i32)
    ensures(
        forall|k: usize| 0 < k < i < nums.len() ==> nums[k] != val
    )
{
}

pub fn main() {
}