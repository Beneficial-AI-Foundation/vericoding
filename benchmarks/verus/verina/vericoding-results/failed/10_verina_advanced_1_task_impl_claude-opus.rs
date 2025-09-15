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
/* helper modified by LLM (iteration 5): implementing proper XOR properties proof */
proof fn lemma_xor_properties(a: i32, b: i32)
    ensures
        a ^ a == 0,
        a ^ 0 == a,
        a ^ b == b ^ a,
        (a ^ b) ^ b == a,
{
    // XOR properties are built into the SMT solver
    // We can use bit-vector reasoning
    assert(a ^ a == 0) by(bit_vector);
    assert(a ^ 0 == a) by(bit_vector);
    assert(a ^ b == b ^ a) by(bit_vector);
    assert((a ^ b) ^ b == a) by(bit_vector);
}

proof fn lemma_xor_accumulator(nums: Seq<i32>, i: nat, acc: i32)
    requires
        i <= nums.len(),
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
        exists|unique_elem: i32| count_occurrences(nums, unique_elem) == 1,
    ensures
        forall|x: i32| #[trigger] count_occurrences(nums.take(i as int), x) == 2 ==> (acc ^ x ^ x == acc),
    decreases nums.len() - i,
{
    if i == 0 {
        assert(nums.take(0).len() == 0);
        assert(forall|x: i32| count_occurrences(nums.take(0), x) == 0);
    } else {
        // Use the XOR cancellation property
        assert(forall|x: i32| {
            lemma_xor_properties(acc, x);
            (x ^ x == 0) && (acc ^ 0 == acc) && (acc ^ x ^ x == acc ^ (x ^ x)) && (acc ^ (x ^ x) == acc ^ 0) && (acc ^ 0 == acc)
        });
    }
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
    /* code modified by LLM (iteration 5): using proper XOR accumulation logic */
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
            exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        decreases nums.len() - i,
    {
        proof {
            lemma_xor_properties(result, nums@[i as int]);
        }
        
        result = result ^ nums[i];
        i = i + 1;
    }
    
    // After XORing all elements, pairs cancel out leaving only the unique element
    proof {
        // XOR is commutative and associative, and x ^ x = 0 for any x
        // So all pairs cancel out, leaving only the unique element
        assert(forall|x: i32| {
            lemma_xor_properties(x, x);
            x ^ x == 0
        });
        
        assert(forall|x: i32| {
            lemma_xor_properties(result, 0);
            result ^ 0 == result
        });
    }
    
    result
}
// </vc-code>

}
fn main() {}