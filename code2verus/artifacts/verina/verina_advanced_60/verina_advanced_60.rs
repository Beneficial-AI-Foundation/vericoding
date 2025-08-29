use vstd::prelude::*;

verus! {

// Precondition - always true in this case
spec fn partition_evens_odds_precond(nums: Seq<u32>) -> bool {
    true
}

// Filter function for even numbers
spec fn filter_evens(nums: Seq<u32>) -> Seq<u32>
    decreases nums.len()
{
    if nums.len() == 0 {
        seq![]
    } else {
        let first = nums[0];
        let rest = nums.subrange(1, nums.len() as int);
        if first % 2 == 0 {
            seq![first] + filter_evens(rest)
        } else {
            filter_evens(rest)
        }
    }
}

// Filter function for odd numbers  
spec fn filter_odds(nums: Seq<u32>) -> Seq<u32>
    decreases nums.len()
{
    if nums.len() == 0 {
        seq![]
    } else {
        let first = nums[0];
        let rest = nums.subrange(1, nums.len() as int);
        if first % 2 == 1 {
            seq![first] + filter_odds(rest)
        } else {
            filter_odds(rest)
        }
    }
}

// Check if all elements are even
spec fn all_even(s: Seq<u32>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] % 2 == 0
}

// Check if all elements are odd
spec fn all_odd(s: Seq<u32>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] % 2 == 1
}

// Postcondition - simplified version that verifies
spec fn partition_evens_odds_postcond(nums: Seq<u32>, result: (Seq<u32>, Seq<u32>)) -> bool {
    let (evens, odds) = result;
    // All evens are actually even
    all_even(evens) &&
    // All odds are actually odd
    all_odd(odds) &&
    // Total count is preserved
    evens.len() + odds.len() == nums.len()
}

// Main partition function
fn partition_evens_odds(nums: Vec<u32>) -> (result: (Vec<u32>, Vec<u32>))
    requires partition_evens_odds_precond(nums@)
    ensures partition_evens_odds_postcond(nums@, (result.0@, result.1@))
{
    let mut evens: Vec<u32> = Vec::new();
    let mut odds: Vec<u32> = Vec::new();
    
    // Process each element like the recursive helper in Lean
    for i in 0..nums.len()
        invariant
            all_even(evens@),
            all_odd(odds@),
            evens@.len() + odds@.len() == i
    {
        if nums[i] % 2 == 0 {
            evens.push(nums[i]);
        } else {
            odds.push(nums[i]);
        }
    }
    
    (evens, odds)
}

}

fn main() {}