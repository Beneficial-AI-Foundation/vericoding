use vstd::prelude::*;

verus! {

// Helper function to get a subarray (slice)
spec fn get_subarray(nums: Seq<u32>, i: int, j: int) -> Seq<u32> {
    if 0 <= i <= j && j < nums.len() {
        nums.subrange(i, j + 1)
    } else {
        seq![]
    }
}

// Helper function to count distinct elements in a sequence
spec fn distinct_count(l: Seq<u32>) -> nat {
    l.to_set().len()
}

// Helper function to square a number
spec fn square(n: nat) -> nat {
    n * n
}

// Precondition for the solution
spec fn solution_precond(nums: Seq<u32>) -> bool {
    1 <= nums.len() && nums.len() <= 100 && 
    forall|i: int| 0 <= i < nums.len() ==> 1 <= nums[i] && nums[i] <= 100
}

// Count distinct elements manually using a simple approach
#[verifier::exec_allows_no_decreases_clause]
fn count_distinct_elements(nums: &Vec<u32>, start: usize, end: usize) -> (count: usize)
    requires 
        start <= end,
        end < nums.len(),
{
    let mut seen = Vec::new();
    let mut k = start;
    
    while k <= end {
        let val = nums[k];
        let mut found = false;
        let mut j = 0;
        
        while j < seen.len() {
            if seen[j] == val {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            seen.push(val);
        }
        k += 1;
    }
    
    seen.len()
}

// Main solution function
#[verifier::exec_allows_no_decreases_clause]
fn solution(nums: Vec<u32>) -> (result: u32)
    requires 
        solution_precond(nums@),
{
    let n = nums.len();
    let mut total_sum = 0u32;
    
    let mut i = 0;
    while i < n {
        let mut d = 0;
        while d < n - i {
            let j = i + d;
            if j < n {
                let count = count_distinct_elements(&nums, i, j);
                #[verifier::truncate]
                let squared = (count * count) as u32;
                total_sum = total_sum + squared;
            }
            d += 1;
        }
        i += 1;
    }
    
    total_sum
}

// Postcondition for the solution
spec fn solution_postcond(nums: Seq<u32>, result: nat) -> bool {
    let n = nums.len();
    
    if !(1 <= n && n <= 100 && forall|i: int| 0 <= i < nums.len() ==> 1 <= nums[i] && nums[i] <= 100) {
        true
    } else {
        result >= 0 &&
        {
            // Calculate expected sum using spec functions
            let expected_sum = spec_calculate_sum(nums, n as int);
            result == expected_sum
        }
    }
}

// Specification function to calculate the expected sum
spec fn spec_calculate_sum(nums: Seq<u32>, n: int) -> nat
    decreases n
{
    if n <= 0 {
        0
    } else {
        spec_outer_sum(nums, n, 0)
    }
}

// Specification function for outer sum calculation
spec fn spec_outer_sum(nums: Seq<u32>, n: int, i: int) -> nat
    decreases (n - i)
{
    if i >= n {
        0
    } else {
        spec_inner_sum(nums, n, i, 0) + spec_outer_sum(nums, n, i + 1)
    }
}

// Specification function for inner sum calculation
spec fn spec_inner_sum(nums: Seq<u32>, n: int, i: int, d: int) -> nat
    decreases (n - i - d)
{
    if i + d >= n {
        0
    } else {
        let j = i + d;
        let subarr = get_subarray(nums, i, j);
        let count = distinct_count(subarr);
        square(count) + spec_inner_sum(nums, n, i, d + 1)
    }
}

fn main() {
    // Test case
    let nums = vec![1, 2, 1];
    assume(solution_precond(nums@));
    let _result = solution(nums);
}

} // verus!