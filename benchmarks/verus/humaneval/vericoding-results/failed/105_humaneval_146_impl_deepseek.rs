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

proof fn count_helper_lemma(nums: Seq<int>, index: int)
    requires
        0 <= index <= nums.len(),
        valid_input(nums)
    ensures
        count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len(),
    decreases nums.len() - index
{
    reveal_with_fuel(count_helper, 2);
    if index < nums.len() {
        count_helper_lemma(nums, index + 1);
    }
}

proof fn count_helper_sat_condition(nums: Seq<int>, index: int, i: int)
    requires
        0 <= index <= nums.len(),
        valid_input(nums),
        index <= i < nums.len(),
        satisfies_condition(nums[i])
    ensures
        count_helper(nums, index) > 0,
    decreases nums.len() - index
{
    reveal_with_fuel(count_helper, 2);
    if index == i {
    } else if index < i {
        count_helper_sat_condition(nums, index + 1, i);
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
    /* code modified by LLM (iteration 5): Fixed type conversion from nat to int for count */
    let mut index: nat = 0;
    let mut count: nat = 0;
    
    while index < nums.len()
        invariant
            count == count_helper(nums, index as int),
            0 <= index <= nums.len(),
            count >= 0,
            count <= nums.len() - index,
        decreases nums.len() - index
    {
        let current = nums@[index];
        if satisfies_condition(current) {
            count = count + 1;
        }
        index = index + 1;
    }
    count as int
}
// </vc-code>


}

fn main() {}