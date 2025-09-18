// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed decreases clause which is not allowed in spec functions */
spec fn get_factor_spec(j: int, k: int, scl: int) -> int {
    if k == 0 {
        1
    } else {
        get_factor_spec(j, k-1, scl) * (scl * 2 * (j - (k-1)))
    }
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 5): fixed implementation to handle m=0 and m=1 cases correctly */
    if m >= c.len() {
        Vec::new()
    } else if m == 0 {
        c.clone()
    } else {
        let capacity = c.len() - m;
        let mut result = Vec::with_capacity(capacity);
        let mut i: usize = 0;
        while i < capacity
            invariant
                i <= capacity,
                result@.len() == i as int,
                forall|t: int| 0 <= t < i as int ==> 
                    result@[t] == c@[t + m as int] * (get_factor_spec(t + m as int, m as int, scl as int) as i32)
        {
            let j = i + m;
            if m == 1 {
                result.push(scl * 2 * (j as i32) * c[j]);
            } else {
                let mut factor = 1;
                let mut k: usize = 0;
                while k < m
                    invariant
                        k <= m,
                        factor == get_factor_spec(j as int, k as int, scl as int) as i32
                {
                    factor = factor * scl * 2 * (j - k) as i32;
                    k += 1;
                }
                result.push(c[j] * factor);
            }
            i += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}