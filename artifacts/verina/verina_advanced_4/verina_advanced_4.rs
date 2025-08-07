use vstd::prelude::*;

verus! {

fn int_max(x: i32, y: i32) -> (result: i32)
    ensures result >= x && result >= y
{
    if x < y { y } else { x }
}

spec fn longest_increasing_subsequence_precond(a: Seq<i32>) -> bool {
    true
}

spec fn longest_increasing_subsequence_postcond(a: Seq<i32>, result: i32) -> bool {
    result >= 0
}

fn longest_increasing_subsequence(a: Vec<i32>) -> (result: i32)
    requires longest_increasing_subsequence_precond(a@)
    ensures longest_increasing_subsequence_postcond(a@, result)
{
    let n = a.len();
    if n == 0 {
        return 0;
    }
    
    let mut dp = Vec::<i32>::new();
    
    // Initialize dp with 1s
    for i in 0..n
        invariant dp.len() == i
    {
        dp.push(1);
    }
    
    // Dynamic programming
    for i in 1..n
        invariant 
            dp.len() == n,
            i <= n
    {
        for j in 0..i
            invariant 
                dp.len() == n,
                j <= i,
                i < n
        {
            if j < a.len() && i < a.len() && a[j] < a[i] {
                // Add overflow protection
                if dp[j] < 1000000 {
                    let new_val = int_max(dp[i], dp[j] + 1);
                    dp.set(i, new_val);
                }
            }
        }
    }
    
    // Find maximum
    let mut max_val = 0i32;
    for i in 0..dp.len()
        invariant max_val >= 0
    {
        max_val = int_max(max_val, dp[i]);
    }
    
    max_val
}

fn main() {}

} // verus!