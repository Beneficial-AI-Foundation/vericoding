// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
    ensures

        result.len() <= maxpower + 1,
        result.len() == if c.len() + (c.len() - 1) * pow <= maxpower + 1 {
            c.len() + (c.len() - 1) * pow
        } else {
            maxpower + 1
        },

        pow == 0 ==> result.len() == 1 && result[0] == 1.0,

        (pow == 1 && c.len() <= maxpower + 1) ==> (
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]
        ),

        ((exists|i: int| 0 <= i < c.len() && c[i] != 0.0) && pow > 0) ==> 
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow issues and postcondition failures */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        return result;
    }
    
    if pow == 1 {
        if c.len() <= maxpower + 1 {
            return c.clone();
        } else {
            let mut result = Vec::new();
            let mut i: usize = 0;
            let limit = maxpower + 1;
            while i < limit
                invariant
                    i <= limit,
                    limit == maxpower + 1,
                    result.len() == i,
                    forall|j: int| 0 <= j < i as int ==> result[j as int] == if (j as int) < c.len() as int { c[j as int] } else { 0.0 },
                decreases limit - i
            {
                if i < c.len() {
                    result.push(c[i]);
                } else {
                    result.push(0.0);
                }
                i = i + 1;
            }
            return result;
        }
    }
    
    let target_len: usize = if c.len() + (c.len() - 1) * pow <= maxpower + 1 {
        c.len() + (c.len() - 1) * pow
    } else {
        maxpower + 1
    };
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < target_len
        invariant
            i <= target_len,
            result.len() == i,
        decreases target_len - i
    {
        result.push(0.0);
        i = i + 1;
    }
    
    result.set(0, 1.0);
    
    let mut p: usize = 0;
    while p < pow
        invariant
            p <= pow,
            result.len() == target_len,
        decreases pow - p
    {
        let mut temp = Vec::new();
        let mut j: usize = 0;
        while j < target_len
            invariant
                j <= target_len,
                temp.len() == j,
            decreases target_len - j
        {
            temp.push(0.0);
            j = j + 1;
        }
        
        let mut k: usize = 0;
        while k < result.len()
            invariant
                k <= result.len(),
                temp.len() == target_len,
            decreases result.len() - k
        {
            if result[k] != 0.0 {
                let mut m: usize = 0;
                while m < c.len()
                    invariant
                        m <= c.len(),
                        temp.len() == target_len,
                        k < result.len(),
                        target_len <= maxpower + 1,
                    decreases c.len() - m
                {
                    if k < target_len && m < target_len && k + m < target_len {
                        let idx = k + m;
                        temp.set(idx, temp[idx] + result[k] * c[m]);
                    }
                    m = m + 1;
                }
            }
            k = k + 1;
        }
        
        result = temp;
        p = p + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}