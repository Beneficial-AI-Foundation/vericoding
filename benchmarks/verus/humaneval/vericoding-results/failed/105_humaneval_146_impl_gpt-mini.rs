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
/* helper modified by LLM (iteration 5): proves count_helper equals set length */
proof fn count_helper_matches_set(nums: Seq<int>, index: int)
    requires 0 <= index <= nums.len(),
    ensures count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len(),
    decreases nums.len() - index
{
    if index == nums.len() {
        assert(count_helper(nums, index) == 0);
        assert(Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len() == 0);
    } else {
        let current = nums[index];
        count_helper_matches_set(nums, index + 1);
        let rest = count_helper(nums, index + 1);
        let rest_len = Set::new(|i: int| index + 1 <= i < nums.len() && satisfies_condition(nums[i])).len();
        assert(rest == rest_len);
        if satisfies_condition(current) {
            assert(count_helper(nums, index) == 1 + rest);
            assert(Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len() == 1 + rest_len);
        } else {
            assert(count_helper(nums, index) == rest);
            assert(Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len() == rest_len);
        }
        assert(count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len());
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
    /* code modified by LLM (iteration 5): use ghost variables for int indices and counts */
    let mut ghost index: int = nums.len() as int;
    let mut ghost count: int = 0;
    while index > 0
        invariant
            0 <= index <= nums.len(),
            count == count_helper(nums, index),
        decreases index
    {
        let i: int = index - 1;
        let ghost i_nat: nat = i as nat;
        if satisfies_condition(nums[i_nat]) {
            count = count + 1;
        }
        index = i;
    }
    proof {
        count_helper_matches_set(nums, 0);
        assert(count == count_helper(nums, 0));
        assert(count == Set::new(|i: int| 0 <= i < nums.len() && satisfies_condition(nums[i])).len());
    }
    count
}

// </vc-code>


}

fn main() {}