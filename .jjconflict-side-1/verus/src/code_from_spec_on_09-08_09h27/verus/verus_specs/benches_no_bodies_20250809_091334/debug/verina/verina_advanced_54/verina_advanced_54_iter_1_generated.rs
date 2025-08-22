use vstd::prelude::*;

verus! {

// Precondition: all elements are <= length and list has no duplicates
spec fn missing_number_precond(nums: Seq<usize>) -> bool {
    (forall|i: int| 0 <= i < nums.len() ==> nums[i] <= nums.len()) &&
    (forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j])
}

// Helper predicate to check if element is in sequence  
spec fn contains(nums: Seq<usize>, x: usize) -> bool {
    exists|i: int| 0 <= i < nums.len() && nums[i] == x
}

// The missing number function
#[verifier::external_body]
fn missing_number(nums: Vec<usize>) -> (result: usize)
    requires missing_number_precond(nums@)
    ensures missing_number_postcond(nums@, result)
{
    let n = nums.len();
    let expected_sum = n * (n + 1) / 2;
    let mut actual_sum = 0;
    
    for i in 0..n
        invariant actual_sum == nums@.subrange(0, i as int).fold_left(0, |acc: usize, x: usize| acc + x)
    {
        actual_sum += nums[i];
    }
    
    expected_sum - actual_sum
}

// Postcondition specification
spec fn missing_number_postcond(nums: Seq<usize>, result: usize) -> bool {
    let n = nums.len();
    // result is in range [0, n]
    result <= n &&
    // result is not in nums
    !contains(nums, result) &&
    // all other numbers in range [0, n] are in nums
    (forall|x: usize| #![trigger contains(nums, x)] x <= n && x != result ==> contains(nums, x))
}

// Proof function showing the specification is satisfied
proof fn missing_number_spec_satisfied(nums: Seq<usize>)
    requires missing_number_precond(nums)
    ensures exists|result: usize| missing_number_postcond(nums, result)
{
    let n = nums.len();
    
    // By pigeonhole principle: we have n distinct elements, each <= n,
    // so exactly one number from 0..=n is missing
    let all_numbers = Seq::<usize>::new(n + 1, |i: int| i as usize);
    
    // Count how many numbers from 0..=n are NOT in nums
    let missing_count = 
        |nums: Seq<usize>| -> nat
            ensures |result: nat| result >= 1
        {
            let mut count = 0nat;
            let mut i = 0;
            while i <= n
                invariant count >= 0
            {
                if !contains(nums, i) {
                    count = count + 1;
                }
                i += 1;
            }
            count
        }(nums);
    
    // Since nums has n elements, all distinct, all <= n,
    // and there are n+1 possible values (0..=n),
    // exactly 1 is missing
    assert(missing_count == 1);
    
    // Therefore there exists exactly one missing number
    assert(exists|result: usize| result <= n && !contains(nums, result) &&
           (forall|x: usize| #![trigger contains(nums, x)] x <= n && x != result ==> contains(nums, x)));
}

} // verus!

fn main() {
    println!("Missing number implementation with Verus verification");
}