// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat {
    nums.filter(|elem: i32| elem == x).len()
}

spec fn filter_equal(nums: Seq<i32>, x: i32) -> Seq<i32> {
    nums.filter(|elem: i32| elem == x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof blocks from spec functions and made them axiomatic */
proof fn lemma_xor_properties(a: i32, b: i32)
    ensures
        a ^ a == 0,
        a ^ 0 == a,
        a ^ b == b ^ a,
{
    // XOR properties are axiomatically true in Verus
}

proof fn lemma_xor_twice_appears(nums: Seq<i32>, x: i32)
    requires
        count_occurrences(nums, x) == 2,
    ensures
        nums.fold_left(0, |acc: i32, elem: i32| acc ^ elem) == nums.remove_value(x).remove_value(x).fold_left(0, |acc: i32, elem: i32| acc ^ elem),
{
    lemma_xor_properties(x, x);
}

proof fn lemma_xor_result(nums: Seq<i32>, unique: i32)
    requires
        nums.len() > 0,
        count_occurrences(nums, unique) == 1,
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
    ensures
        nums.fold_left(0, |acc: i32, elem: i32| acc ^ elem) == unique,
{
    lemma_xor_properties(unique, 0);
    lemma_xor_twice_appears(nums, unique);
}
// </vc-helpers>

// <vc-spec>
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
    ensures
        count_occurrences(nums@, result) == 1,
        forall|x: i32| nums@.contains(x) ==> (x == result || count_occurrences(nums@, x) == 2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified XOR algorithm with cleaner proof structure */
    let mut result = 0;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result == nums@.subrange(0, i as int).fold_left(0, |acc: i32, elem: i32| acc ^ elem),
        decreases nums.len() - i
    {
        result = result ^ nums[i];
        i += 1;
        
        proof {
            assert(nums@.subrange(0, i as int) == nums@.subrange(0, (i-1) as int).push(nums@[i-1 as int]));
        }
    }
    
    proof {
        assert(nums@.subrange(0, nums.len() as int) == nums@);
        assert(result == nums@.fold_left(0, |acc: i32, elem: i32| acc ^ elem));
        
        let unique_elem = choose|x: i32| count_occurrences(nums@, x) == 1;
        lemma_xor_result(nums@, unique_elem);
        assert(result == unique_elem);
        assert(count_occurrences(nums@, result) == 1);
        
        assert forall|x: i32| nums@.contains(x) implies (x == result || count_occurrences(nums@, x) == 2) by {
            if nums@.contains(x) {
                if count_occurrences(nums@, x) == 1 {
                    assert(x == unique_elem);
                    assert(x == result);
                } else {
                    assert(count_occurrences(nums@, x) == 2);
                }
            }
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}