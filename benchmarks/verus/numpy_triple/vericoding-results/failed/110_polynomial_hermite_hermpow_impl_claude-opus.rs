// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added safe addition helper to prevent overflow */
fn safe_add(a: usize, b: usize) -> (result: usize)
    ensures
        a <= usize::MAX - b ==> result == a + b,
        a > usize::MAX - b ==> result == usize::MAX
{
    if a <= usize::MAX - b { a + b } else { usize::MAX }
}
// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        maxpower >= 0,
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
/* code modified by LLM (iteration 5): Fixed arithmetic overflow checks and loop bounds */
{
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        assert(result.len() == 1);
        assert(result[0] == 1.0);
        return result;
    }
    
    if pow == 1 {
        let target_len = if c.len() <= safe_add(maxpower, 1) { c.len() } else { safe_add(maxpower, 1) };
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < target_len
            invariant
                i <= target_len,
                target_len <= c.len(),
                target_len <= safe_add(maxpower, 1),
                result.len() == i,
                forall|j: int| 0 <= j < i as int ==> result[j as int] == c[j as int]
            decreases target_len - i
        {
            result.push(c[i]);
            i = i + 1;
        }
        return result;
    }
    
    let mut current = c.clone();
    let mut p: usize = 1;
    
    while p < pow
        invariant
            p >= 1,
            p <= pow,
            current.len() > 0,
            current.len() <= safe_add(maxpower, 1)
        decreases pow - p
    {
        let mut next = Vec::new();
        let current_plus_c = if current.len() + c.len() > 1 { 
            safe_add(safe_add(current.len(), c.len()), if current.len() + c.len() >= 1 { -1usize } else { 0 })
        } else { 
            1 
        };
        let target_size = if current_plus_c <= safe_add(maxpower, 1) { current_plus_c } else { safe_add(maxpower, 1) };
        let mut i: usize = 0;
        
        while i < target_size
            invariant
                i <= target_size,
                next.len() == i,
                target_size <= safe_add(maxpower, 1)
            decreases target_size - i
        {
            let mut sum = 0.0;
            let mut j: usize = 0;
            let max_j = if i < current.len() { i } else { if current.len() > 0 { current.len() - 1 } else { 0 } };
            
            while j <= max_j
                invariant
                    j <= max_j + 1,
                    current.len() > 0,
                    max_j < current.len()
                decreases max_j + 1 - j
            {
                if j < current.len() && i >= j && i - j < c.len() {
                    sum = sum + current[j] * c[i - j];
                }
                j = j + 1;
            }
            
            next.push(sum);
            i = i + 1;
        }
        
        current = next;
        p = p + 1;
    }
    
    current
}
// </vc-code>

}
fn main() {}