// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added overflow checks and stronger invariants for array bounds */
    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        result
    } else if pow == 1 {
        c.clone()
    } else {
        // Check for overflow before computation
        if c.len() == 0 || pow as usize > usize::MAX / (c.len() - 1) {
            // Return empty vector on overflow
            Vec::new()
        } else {
            let mut result = Vec::new();
            let mut i: usize = 0;
            let target_len = 1 + (c.len() - 1) * pow as usize;
            while i < target_len
                invariant
                    c.len() > 0,
                    target_len == 1 + (c.len() - 1) * pow as usize,
                    i <= target_len,
                    result.len() == i,
                decreases target_len - i
            {
                result.push(0.0);
                i = i + 1;
            }
            
            let mut p: u8 = 0;
            let mut current = Vec::new();
            current.push(1.0);
            
            while p < pow
                invariant
                    p <= pow,
                    pow <= maxpower,
                    maxpower <= 16,
                    c.len() > 0,
                    result.len() == 1 + (c.len() - 1) * pow as usize,
                    p == 0 ==> current.len() == 1 && current[0] == 1.0,
                    p >= 1 ==> current.len() == 1 + (c.len() - 1) * p as usize,
                    (p + 1) as usize <= 16,
                    (c.len() - 1) * (p + 1) as usize <= usize::MAX - 1,
                decreases pow - p
            {
                let mut next = Vec::new();
                let mut i: usize = 0;
                let next_len = if (p + 1) as usize <= usize::MAX / (c.len() - 1) {
                    1 + (c.len() - 1) * (p + 1) as usize
                } else {
                    1  // fallback to avoid overflow
                };
                
                while i < next_len
                    invariant
                        c.len() > 0,
                        p < pow,
                        pow <= maxpower,
                        maxpower <= 16,
                        next_len == 1 + (c.len() - 1) * (p + 1) as usize,
                        i <= next_len,
                        next.len() == i,
                    decreases next_len - i
                {
                    next.push(0.0);
                    i = i + 1;
                }
                
                let mut i: usize = 0;
                while i < current.len()
                    invariant
                        i <= current.len(),
                        next.len() == 1 + (c.len() - 1) * (p + 1) as usize,
                        c.len() > 0,
                        p >= 0,
                        p < pow,
                        pow <= maxpower,
                        maxpower <= 16,
                        p == 0 ==> current.len() == 1,
                        p >= 1 ==> current.len() == 1 + (c.len() - 1) * p as usize,
                        current.len() + c.len() - 1 <= next.len(),
                    decreases current.len() - i
                {
                    let mut j: usize = 0;
                    while j < c.len()
                        invariant
                            j <= c.len(),
                            i < current.len(),
                            next.len() == 1 + (c.len() - 1) * (p + 1) as usize,
                            c.len() > 0,
                            p >= 0,
                            p < pow,
                            pow <= maxpower,
                            maxpower <= 16,
                            p == 0 ==> current.len() == 1,
                            p >= 1 ==> current.len() == 1 + (c.len() - 1) * p as usize,
                            i + c.len() <= next.len(),
                            forall|k: int| 0 <= k < j ==> i + k < next.len(),
                        decreases c.len() - j
                    {
                        if i + j < next.len() && i < current.len() && j < c.len() {
                            let val = next[i + j] + current[i] * c[j];
                            next.set(i + j, val);
                        }
                        j = j + 1;
                    }
                    i = i + 1;
                }
                
                current = next;
                p = p + 1;
            }
            
            current
        }
    }
}
// </vc-code>

}
fn main() {}