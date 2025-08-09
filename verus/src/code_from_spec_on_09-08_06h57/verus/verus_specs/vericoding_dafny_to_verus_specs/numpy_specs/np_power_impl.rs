use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

fn power(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for outer loop termination */
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> #[trigger] result[i] == pow(a[i] as int, b[i] as nat),
        decreases a.len() - idx
    {
        let base = a[idx];
        let exp = b[idx];
        
        // Compute base^exp
        let mut power_result = 1i32;
        let mut e = exp;
        
        /* code modified by LLM (iteration 1): added decreases clause for inner loop termination */
        while e > 0
            invariant
                power_result as int * pow(base as int, e as nat) == pow(base as int, exp as nat),
            decreases e
        {
            power_result = power_result * base;
            e = e - 1;
        }
        
        result.push(power_result);
        idx = idx + 1;
    }
    
    result
}

fn main() {}

}