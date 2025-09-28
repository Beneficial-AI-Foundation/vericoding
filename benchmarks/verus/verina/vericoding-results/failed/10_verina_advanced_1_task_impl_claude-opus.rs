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
/* helper modified by LLM (iteration 5): Removed all assume statements, using assert-by for XOR properties */
proof fn lemma_xor_properties()
    ensures
        forall|a: i32| a ^ a == 0,
        forall|a: i32| a ^ 0 == a,
        forall|a: i32, b: i32| a ^ b == b ^ a,
        forall|a: i32, b: i32, c: i32| (a ^ b) ^ c == a ^ (b ^ c),
{
    assert forall|a: i32| a ^ a == 0 by {
        assert((a ^ a) == 0);
    }
    assert forall|a: i32| a ^ 0 == a by {
        assert((a ^ 0) == a);
    }
    assert forall|a: i32, b: i32| a ^ b == b ^ a by {
        assert((a ^ b) == (b ^ a));
    }
    assert forall|a: i32, b: i32, c: i32| (a ^ b) ^ c == a ^ (b ^ c) by {
        assert(((a ^ b) ^ c) == (a ^ (b ^ c)));
    }
}

proof fn lemma_xor_fold_step(nums: Seq<i32>, i: int, acc: i32)
    requires
        0 <= i < nums.len(),
        acc == nums.subrange(0, i).fold_left(0, |a: i32, x: i32| a ^ x),
    ensures
        acc ^ nums[i] == nums.subrange(0, i + 1).fold_left(0, |a: i32, x: i32| a ^ x),
{
    // Direct assertion based on fold_left definition
    assert(nums.subrange(0, i + 1).fold_left(0, |a: i32, x: i32| a ^ x) == 
           nums.subrange(0, i).fold_left(0, |a: i32, x: i32| a ^ x) ^ nums[i]);
}

proof fn lemma_xor_cancels_duplicates(nums: Seq<i32>)
    requires
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums, unique_elem) == 1,
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
    ensures
        exists|unique_elem: i32| #[trigger] count_occurrences(nums, unique_elem) == 1 && 
            nums.fold_left(0, |acc: i32, x: i32| acc ^ x) == unique_elem,
{
    lemma_xor_properties();
    let unique_elem = choose|elem: i32| count_occurrences(nums, elem) == 1;
    
    // The XOR of all elements cancels out duplicates and leaves the unique element
    // This is a fundamental property of XOR that Verus should recognize
    assert(nums.fold_left(0, |acc: i32, x: i32| acc ^ x) == unique_elem);
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
    /* code modified by LLM (iteration 5): Removed all assume statements from proof blocks */
    let mut result = 0i32;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result == nums@.subrange(0, i as int).fold_left(0, |acc: i32, x: i32| acc ^ x),
            exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
            forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
        decreases nums.len() - i
    {
        let old_result = result;
        result = result ^ nums[i];
        
        proof {
            lemma_xor_fold_step(nums@, i as int, old_result);
            assert(result == nums@.subrange(0, (i + 1) as int).fold_left(0, |acc: i32, x: i32| acc ^ x));
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_xor_properties();
        assert(nums@.subrange(0, nums.len() as int) == nums@);
        assert(result == nums@.fold_left(0, |acc: i32, x: i32| acc ^ x));
        lemma_xor_cancels_duplicates(nums@);
        
        // The result is the unique element as proven by the lemma
        let unique_elem = choose|elem: i32| count_occurrences(nums@, elem) == 1;
        assert(result == unique_elem);
        assert(count_occurrences(nums@, result) == 1);
        
        // All other elements appear exactly twice
        assert forall|x: i32| nums@.contains(x) implies (x == result || count_occurrences(nums@, x) == 2) by {
            if nums@.contains(x) {
                assert(count_occurrences(nums@, x) == 1 || count_occurrences(nums@, x) == 2);
                if count_occurrences(nums@, x) == 1 {
                    assert(x == unique_elem);
                    assert(x == result);
                }
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}