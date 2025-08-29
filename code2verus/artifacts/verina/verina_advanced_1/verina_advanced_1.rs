use vstd::prelude::*;

verus! {

// Helper function to filter a list by a specific value (equivalent to Lean's filterlist)
fn filterlist(x: i32, nums: &Vec<i32>) -> (result: Vec<i32>)
{
    let mut result = Vec::new();
    for i in 0..nums.len() {
        if nums[i] == x {
            result.push(nums[i]);
        }
    }
    result
}

// Count how many times a value appears in the sequence
spec fn count_in_seq(s: Seq<i32>, x: i32) -> nat {
    s.filter(|y: i32| y == x).len()
}

// Precondition specification
spec fn find_single_number_precond(nums: Seq<i32>) -> bool {
    &&& (forall|x: i32| nums.contains(x) ==> {
        let count = count_in_seq(nums, x);
        count == 1 || count == 2
    })
    &&& (exists|x: i32| nums.contains(x) && count_in_seq(nums, x) == 1)
    &&& (forall|x: i32, y: i32| 
        nums.contains(x) && nums.contains(y) && 
        count_in_seq(nums, x) == 1 && count_in_seq(nums, y) == 1 ==> 
        x == y)
}

// Main function that finds the single number
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
{
    for i in 0..nums.len() {
        let x = nums[i];
        let filtered = filterlist(x, nums);
        let count = filtered.len();
        
        if count == 1 {
            return x;
        }
    }
    
    // Default return - should not be reached with valid input
    nums[0]
}

// Postcondition specification  
spec fn find_single_number_postcond(nums: Seq<i32>, result: i32) -> bool {
    &&& nums.len() > 0
    &&& count_in_seq(nums, result) == 1  
    &&& (forall|x: i32| nums.contains(x) ==> (x == result || count_in_seq(nums, x) == 2))
}

fn main() {}

} // verus!