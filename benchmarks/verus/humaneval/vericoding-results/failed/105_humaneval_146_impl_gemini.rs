// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn first_digit(n: int) -> int
    recommends n > 0
    decreases n
{
    if n < 10 { n } else { first_digit(n / 10) }
}

spec fn last_digit(n: int) -> int
    recommends n > 0
{
    n % 10
}

spec fn is_odd(n: int) -> bool
{
    n == 1 || n == 3 || n == 5 || n == 7 || n == 9
}

spec fn satisfies_condition(n: int) -> bool
{
    n > 10 && is_odd(first_digit(n)) && is_odd(last_digit(n))
}

spec fn valid_input(nums: Seq<int>) -> bool
{
    true
}
spec fn count_helper(nums: Seq<int>, index: int) -> int
    recommends 0 <= index <= nums.len()
    decreases nums.len() - index when 0 <= index <= nums.len()
{
    if index == nums.len() {
        0
    } else {
        let current = nums[index];
        let contribution: int = if satisfies_condition(current) { 1 } else { 0 };
        contribution + count_helper(nums, index + 1)
    }
}

// </vc-preamble>

// <vc-helpers>
proof fn count_helper_property(nums: Seq<int>, i: int)
    requires 0 <= i <= nums.len()
    ensures
        count_helper(nums, i) ==
            Set::new(|j: int| i <= j < nums.len() && satisfies_condition(nums[j])).len()
    decreases nums.len() - i
{
    if i < nums.len() {
        count_helper_property(nums, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn special_filter(nums: Seq<int>) -> (count: int)
    requires 
        valid_input(nums)
    ensures 
        count >= 0,
        count <= nums.len(),
        count == Set::new(|i: int| 0 <= i < nums.len() && satisfies_condition(nums[i])).len(),
        nums.len() == 0 ==> count == 0,
        forall|i: int| #![auto] 0 <= i < nums.len() && satisfies_condition(nums[i]) ==> 
            nums[i] > 10 && is_odd(first_digit(nums[i])) && is_odd(last_digit(nums[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut count: int = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            count >= 0,
            count <= i,
            count == Set::new(|j: int| 0 <= j < i && satisfies_condition(nums[j])).len(),
            forall|k: int| 0 <= k < i && satisfies_condition(nums[k]) ==>
                nums[k] > 10 && is_odd(first_digit(nums[k])) && is_odd(last_digit(nums[k])),
        decreases nums.len() - i
    {
        if satisfies_condition(nums[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}