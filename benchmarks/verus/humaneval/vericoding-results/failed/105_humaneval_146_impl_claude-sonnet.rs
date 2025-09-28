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
/* helper modified by LLM (iteration 5): fixed type mismatches for nat/int conversions and sequence indexing */
fn lemma_count_helper_correct(nums: Seq<int>, index: int)
    requires 0 <= index <= nums.len()
    ensures count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums@[i])).len()
    decreases nums.len() - index
{
    if index == nums.len() as int {
        assert(Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums@[i])) =~= Set::empty());
    } else {
        lemma_count_helper_correct(nums, index + 1);
        let s1 = Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums@[i]));
        let s2 = Set::new(|i: int| (index + 1) <= i < nums.len() && satisfies_condition(nums@[i]));
        if satisfies_condition(nums@[index]) {
            assert(s1 =~= s2.insert(index));
        } else {
            assert(s1 =~= s2);
        }
    }
}

fn lemma_first_digit_bounds(n: int)
    requires n > 0
    ensures 1 <= first_digit(n) <= 9
    decreases n
{
    if n < 10 {
    } else {
        lemma_first_digit_bounds(n / 10);
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
    /* code modified by LLM (iteration 5): fixed type mismatches for usize/nat conversions and sequence indexing */
    let mut count: int = 0;
    let mut i: usize = 0;
    
    while i < nums.len() as usize
        invariant
            0 <= i <= nums.len(),
            count >= 0,
            count == Set::new(|j: int| 0 <= j < i && satisfies_condition(nums@[j])).len()
    {
        let current = nums@[i as int];
        
        if current > 10 {
            proof {
                if current > 0 {
                    lemma_first_digit_bounds(current);
                }
            }
            
            let first = first_digit(current);
            let last = last_digit(current);
            
            if is_odd(first) && is_odd(last) {
                count = count + 1;
            }
        }
        
        proof {
            let old_set = Set::new(|j: int| 0 <= j < i && satisfies_condition(nums@[j]));
            let new_set = Set::new(|j: int| 0 <= j < i + 1 && satisfies_condition(nums@[j]));
            let idx = i as int;
            
            if satisfies_condition(nums@[idx]) {
                assert(new_set =~= old_set.insert(idx));
            } else {
                assert(new_set =~= old_set);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_count_helper_correct(nums, 0);
        assert(Set::new(|j: int| 0 <= j < nums.len() && satisfies_condition(nums@[j])) =~= 
               Set::new(|j: int| 0 <= j < i && satisfies_condition(nums@[j])));
    }
    
    count
}
// </vc-code>


}

fn main() {}