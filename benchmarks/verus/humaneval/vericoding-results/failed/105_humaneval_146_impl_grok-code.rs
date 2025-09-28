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
/* helper modified by LLM (iteration 5): Adjusted literals to int type in exec functions */
exec fn first_digit_exec(n: int) -> (fd: int)
    requires
        n > 0,
    ensures
        fd == first_digit(n),
{
    let mut m: int = n;
    while m >= 10int
        invariant
            m > 0,
            first_digit(m) == first_digit(n),
        decreases m,
    {
        m = m / 10int;
    }
    m
}

/* helper modified by LLM (iteration 5): Adjusted literals to int type in exec functions */
exec fn last_digit_exec(n: int) -> (ld: int)
    ensures
        ld == last_digit(n),
{
    n % 10int
}

/* helper modified by LLM (iteration 5): Adjusted literals to int type in exec functions */
exec fn is_odd_exec(d: int) -> bool
{
    d == 1int || d == 3int || d == 5int || d == 7int || d == 9int
}

/* helper modified by LLM (iteration 5): Adjusted literals to int type in exec functions */
exec fn satisfies_condition_exec(n: int) -> (res: bool)
    ensures
        res == satisfies_condition(n),
{
    if n <= 10int { false } else {
        let fd: int = first_digit_exec(n);
        let ld: int = last_digit_exec(n);
        is_odd_exec(fd) && is_odd_exec(ld)
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
/* code modified by LLM (iteration 5): Fixed types for loop variables and operations */
{
    let mut i: nat = 0;
    let mut count: int = 0;
    while i < nums.len()
        invariant
            0nat <= i <= nums.len(),
            0int <= count <= i,
            count == Set::new(|j: int| 0 <= j < i && satisfies_condition(nums[j])).len(),
        decreases nums.len() - i,
    {
        let current: int = nums@[i];
        if satisfies_condition_exec(current) {
            count = count + 1int;
        }
        i = i + 1nat;
    }
    count
}
// </vc-code>


}

fn main() {}