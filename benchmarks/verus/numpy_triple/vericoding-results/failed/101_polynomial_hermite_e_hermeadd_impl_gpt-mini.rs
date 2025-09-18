// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [compute max of two nat values] */
fn max(a: nat, b: nat) -> nat { if a >= b { a } else { b } }
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
    /* code modified by LLM (iteration 5): [use proper invariant syntax without extra parentheses and sum coefficients] */
    let n1 = c1.len();
    let n2 = c2.len();
    let max_len = if n1 >= n2 { n1 } else { n2 };
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < max_len
        invariant result.len() == i,
        invariant forall |j: nat| j < i ==> result@[j] == (if j < n1 { c1@[j] } else { 0 }) + (if j < n2 { c2@[j] } else { 0 }),
        decreases max_len - i
    {
        let coeff1 = if i < n1 { c1[i] } else { 0 };
        let coeff2 = if i < n2 { c2[i] } else { 0 };
        result.push(coeff1 + coeff2);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}