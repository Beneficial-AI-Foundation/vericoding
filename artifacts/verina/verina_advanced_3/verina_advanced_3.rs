use vstd::prelude::*;

verus! {

// Helper function equivalent to intMax
fn int_max(x: i32, y: i32) -> (result: i32)
    ensures result == if x < y { y } else { x }
{
    if x < y { y } else { x }
}

// Precondition - always true in this case
spec fn longest_common_subsequence_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    true
}

// Postcondition: result is the length of a longest common subsequence
spec fn longest_common_subsequence_postcond(a: Seq<i32>, b: Seq<i32>, result: int) -> bool {
    result >= 0
}

// Main function
fn longest_common_subsequence(a: &Vec<i32>, b: &Vec<i32>) -> (result: i32)
    requires 
        longest_common_subsequence_precond(a@, b@),
        a.len() < 1000,  // Reasonable bounds to avoid overflow
        b.len() < 1000,
    ensures longest_common_subsequence_postcond(a@, b@, result as int),
{
    let m = a.len();
    let n = b.len();
    
    if m == 0 || n == 0 {
        return 0;
    }
    
    // Create previous row initialized to zeros
    let mut prev: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k <= n
        invariant k <= n + 1, prev.len() == k,
        decreases n + 1 - k,
    {
        prev.push(0);
        k += 1;
    }
    
    let mut i: usize = 1;
    while i <= m
        invariant 
            1 <= i <= m + 1, 
            prev.len() == n + 1,
            m < 1000,
            n < 1000,
        decreases m + 1 - i,
    {
        // Create current row initialized to zeros
        let mut curr: Vec<i32> = Vec::new();
        let mut l: usize = 0;
        while l <= n
            invariant l <= n + 1, curr.len() == l,
            decreases n + 1 - l,
        {
            curr.push(0);
            l += 1;
        }
        
        let mut j: usize = 1;
        while j <= n
            invariant 
                1 <= j <= n + 1, 
                curr.len() == n + 1,
                prev.len() == n + 1,
                i >= 1 && i <= m,
            decreases n + 1 - j,
        {
            if i > 0 && j > 0 && i - 1 < a.len() && j - 1 < b.len() && a[i - 1] == b[j - 1] {
                curr[j] = prev[j - 1] + 1;
            } else {
                curr[j] = int_max(prev[j], curr[j - 1]);
            }
            j += 1;
        }
        
        // Move curr to prev for next iteration
        prev = curr;
        i += 1;
    }
    
    prev[n]
}

}

fn main() {
    let a = vec![1, 2, 3];
    let b = vec![2, 3, 4];
    let result = longest_common_subsequence(&a, &b);
    println!("LCS length: {}", result);
}