use vstd::prelude::*;

verus! {

fn int_max(x: i32, y: i32) -> (result: i32)
    ensures result >= x && result >= y
{
    if x >= y {
        x
    } else {
        y
    }
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
    
    /* code modified by LLM (iteration 1): added explicit type annotation for dp */
    let mut dp: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant 
            i <= n,
            dp.len() == i,
            forall |j: int| 0 <= j < i ==> dp@[j] >= 1
    {
        let mut max_len = 1;
        let mut j = 0;
        
        while j < i
            invariant
                j <= i,
                max_len >= 1,
                /* code modified by LLM (iteration 1): fixed type mismatch by casting i to int */
                forall |k: int| 0 <= k < j && a@[k] < a@[i as int] ==> max_len >= dp@[k] + 1
        {
            if a[j] < a[i] && dp[j] + 1 > max_len {
                max_len = dp[j] + 1;
            }
            j += 1;
        }
        
        dp.push(max_len);
        i += 1;
    }
    
    let mut result = 0;
    let mut k = 0;
    
    while k < dp.len()
        invariant
            k <= dp.len(),
            result >= 0,
            forall |j: int| 0 <= j < k ==> result >= dp@[j]
    {
        if dp[k] > result {
            result = dp[k];
        }
        k += 1;
    }
    
    result
}

fn main() {}

} // verus!