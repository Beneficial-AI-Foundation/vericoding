// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): added decreases clauses to all loops */
    if m >= c.len() {
        return Vec::new();
    }
    let end_index: usize = c.len() - m;
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < end_index
        invariant
            result.len() == i,
        decreases end_index - i
    {
        let mut scl_power: i64 = 1;
        let mut power_loop: usize = 0;
        while power_loop < m
            invariant
                0 <= power_loop <= m,
            decreases m - power_loop
        {
            scl_power = scl_power * (scl as i64);
            power_loop += 1;
        }
        let mut prod: i64 = 1;
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
            decreases m - j
        {
            let idx = i + m - j;
            prod = prod * (2_i64 * (idx as i64));
            j += 1;
        }
        let coeff = ((prod * scl_power * (c[i + m] as i64)) as i8);
        result.push(coeff);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}