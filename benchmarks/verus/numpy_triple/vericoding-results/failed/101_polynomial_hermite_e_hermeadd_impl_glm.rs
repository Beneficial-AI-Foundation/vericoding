// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn get_default_exec(v: Vec<i32>, i: usize) -> i32
{
    if i < v.len() {
        v[i]
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);

    for i in 0..max_len
        invariant
            0 <= i <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> {
                let coeff1 = if (j as usize) < c1.len() { c1[j as usize] } else { 0 };
                let coeff2 = if (j as usize) < c2.len() { c2[j as usize] } else { 0 };
                #[trigger] result[j as usize] == coeff1 + coeff2
            }
    {
        let coeff1 = get_default_exec(c1, i);
        let coeff2 = get_default_exec(c2, i);
        result.push(coeff1 + coeff2);
    }

    result
}
// </vc-code>

}
fn main() {}