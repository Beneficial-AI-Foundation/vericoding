// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] as int == c1[i] as int
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == c2[i] as int
            } else {
                result[i] as int == 0
            }
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error and corrected loop logic */
{
    let c1_len = c1.len();
    let c2_len = c2.len();
    let res_len = if c1_len >= c2_len { c1_len } else { c2_len };

    let mut result = Vec::with_capacity(res_len);
    let mut i: usize = 0;
    while i < res_len
        invariant
            0 <= i <= res_len,
            result.len() == i,
            res_len == (if c1.len() >= c2.len() { c1.len() } else { c2.len() }),
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result@[j] as int == c1@[j] as int + c2@[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result@[j] as int == c1@[j] as int
                } else if j >= c1.len() && j < c2.len() {
                    result@[j] as int == c2@[j] as int
                } else {
                    true
                }
            },
        decreases res_len - i
    {
        let val = if i < c1_len && i < c2_len {
            c1[i] + c2[i]
        } else if i < c1_len {
            c1[i]
        } else {
            c2[i]
        };
        result.push(val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}