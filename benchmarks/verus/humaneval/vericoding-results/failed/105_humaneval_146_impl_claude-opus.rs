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
/* helper modified by LLM (iteration 4): Fixed type annotations and generic parameter */
proof fn lemma_count_helper_bounds(nums: Seq<int>, index: int)
    requires
        0 <= index <= nums.len()
    ensures
        0 <= count_helper(nums, index) <= nums.len() - index
    decreases nums.len() - index
{
    if index == nums.len() {
        assert(count_helper(nums, index) == 0);
    } else {
        lemma_count_helper_bounds(nums, index + 1);
        assert(count_helper(nums, index + 1) >= 0);
        assert(count_helper(nums, index + 1) <= nums.len() - index - 1);
        let contribution: int = if satisfies_condition(nums[index]) { 1 } else { 0 };
        assert(contribution >= 0 && contribution <= 1);
        assert(count_helper(nums, index) == contribution + count_helper(nums, index + 1));
    }
}

proof fn lemma_count_helper_equals_set(nums: Seq<int>, index: int)
    requires
        0 <= index <= nums.len()
    ensures
        count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len()
    decreases nums.len() - index
{
    if index == nums.len() {
        assert(Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])) =~= Set::<int>::empty());
        assert(Set::<int>::empty().len() == 0);
    } else {
        lemma_count_helper_equals_set(nums, index + 1);
        let set_current = Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i]));
        let set_rest = Set::new(|i: int| index + 1 <= i < nums.len() && satisfies_condition(nums[i]));
        
        if satisfies_condition(nums[index]) {
            assert(set_current =~= set_rest.insert(index));
            assert(!(set_rest.contains(index)));
            assert(set_current.len() == set_rest.len() + 1);
        } else {
            assert(set_current =~= set_rest);
            assert(set_current.len() == set_rest.len());
        }
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
    /* code modified by LLM (iteration 4): Fixed type system by using usize for loop counter */
    let mut count: int = 0;
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            count == count_helper(nums, 0) - count_helper(nums, i as int),
            count == Set::new(|j: int| 0 <= j < i as int && satisfies_condition(nums[j])).len()
        decreases nums.len() - i
    {
        proof {
            lemma_count_helper_bounds(nums, i as int);
            lemma_count_helper_equals_set(nums, 0);
            lemma_count_helper_equals_set(nums, i as int);
            lemma_count_helper_equals_set(nums, (i + 1) as int);
        }
        
        if satisfies_condition(nums@[i as int]) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_count_helper_equals_set(nums, 0);
        assert(count_helper(nums, nums.len() as int) == 0);
        assert(count == count_helper(nums, 0));
        assert(Set::new(|j: int| 0 <= j < nums.len() && satisfies_condition(nums[j])) =~= 
               Set::new(|j: int| 0 <= j < nums.len() && satisfies_condition(nums[j])));
    }
    
    count
}
// </vc-code>


}

fn main() {}