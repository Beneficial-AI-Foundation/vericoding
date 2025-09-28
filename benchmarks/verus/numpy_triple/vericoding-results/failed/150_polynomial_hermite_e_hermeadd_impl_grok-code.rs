// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed quantifier trigger by adding #[trigger] and removed verification assume */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i = 0;
    while i < max_len
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < result.len() ==> {
                let coeff1_j = if j < c1@.len() { c1@[j] as int } else { 0 };
                let coeff2_j = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == coeff1_j + coeff2_j
            },
        decreases max_len - i
    {
        let coeff1 = if i < c1.len() { c1[i] } else { 0i8 };
        let coeff2 = if i < c2.len() { c2[i] } else { 0i8 };
        let sum_int = coeff1 as i32 + coeff2 as i32;
        result.push(sum_int as i8);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}