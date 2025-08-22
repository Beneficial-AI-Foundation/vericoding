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
    
    let mut dp: Vec<i32> = Vec::with_capacity(n);
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < n
        invariant 
            i <= n,
            dp.len() == i,
            forall|j: int| 0 <= j < i ==> dp@[j] >= 1
        decreases n - i
    {
        let mut max_len = 1;
        let mut j = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        while j < i
            invariant
                j <= i,
                max_len >= 1,
                forall|k: int| 0 <= k < j && a@[k] < a@[i as int] ==> max_len >= dp@[k] + 1
            decreases i - j
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
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while k < dp.len()
        invariant
            k <= dp.len(),
            result >= 0,
            forall|j: int| 0 <= j < k ==> result >= dp@[j]
        decreases dp.len() - k
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