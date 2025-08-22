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
    return 0;  // TODO: Remove this line and implement the function body
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
    admit();
}

} // verus!

fn main() {
    // TODO: Remove this comment and implement the function body
}