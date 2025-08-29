use vstd::prelude::*;

verus! {

// Helper function to check if a sequence is sorted
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] <= s[i + 1]
}

// Helper function to perform right rotation by 1 position
spec fn right_shift_one(s: Seq<int>) -> Seq<int> {
    if s.len() == 0 {
        s
    } else {
        seq![s[s.len() - 1]] + s.subrange(0, s.len() - 1)
    }
}

// Helper function to perform right rotation by k positions
spec fn right_shift(k: nat, s: Seq<int>) -> Seq<int>
    decreases k
{
    if k == 0 {
        s
    } else {
        right_shift((k - 1) as nat, right_shift_one(s))
    }
}

// Precondition: list has no duplicates
spec fn minimum_right_shifts_precond(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] != #[trigger] nums[j]
}

// Postcondition specification
spec fn minimum_right_shifts_postcond(nums: Seq<int>, result: int) -> bool {
    let n = nums.len();
    
    if n <= 1 {
        result == 0
    } else if result >= 0 {
        result < n &&
        is_sorted(right_shift(result as nat, nums)) &&
        forall|j: nat| j < result ==> !is_sorted(#[trigger] right_shift(j, nums))
    } else {
        result == -1 &&
        forall|k: nat| k < n ==> !is_sorted(#[trigger] right_shift(k, nums))
    }
}

// Helper function to check if a vector is sorted
#[verifier::external_body]
fn is_sorted_aux(nums: &Vec<i32>) -> (result: bool) {
    if nums.len() <= 1 {
        return true;
    }
    
    for i in 0..(nums.len() - 1) {
        if nums[i] > nums[i + 1] {
            return false;
        }
    }
    true
}

// Helper function to perform a single right shift
#[verifier::external_body]
fn right_shift_once(nums: &Vec<i32>) -> (result: Vec<i32>) {
    if nums.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    result.push(nums[nums.len() - 1]);
    
    for i in 0..(nums.len() - 1) {
        result.push(nums[i]);
    }
    result
}

#[verifier::external_body]
fn minimum_right_shifts(nums: Vec<i32>) -> (result: i32)
    requires minimum_right_shifts_precond(nums@.map(|i, x| x as int))
    ensures minimum_right_shifts_postcond(nums@.map(|i, x| x as int), result as int)
{
    let n = nums.len();
    
    // Base cases: empty or single element list is already sorted
    if n <= 1 {
        return 0;
    }
    
    // Check if the input list is already sorted
    if is_sorted_aux(&nums) {
        return 0;
    }
    
    // Check subsequent shifts
    let mut shifts_count = 1;
    let mut current_list = right_shift_once(&nums);
    
    while shifts_count < n {
        if is_sorted_aux(&current_list) {
            return shifts_count as i32;
        }
        shifts_count += 1;
        if shifts_count < n {
            current_list = right_shift_once(&current_list);
        }
    }
    
    -1
}

} // verus!

fn main() {}