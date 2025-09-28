// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [empty helper section] */
// </vc-helpers>

// <vc-spec>
fn polysub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int - c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] == c1[i]
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == 0 - c2[i] as int
            } else {
                result[i] == 0
            }
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fix type mismatches by casting usize to int where necessary for indexing] */
{
    let len1 = c1.len(); // len1 is usize
    let len2 = c2.len(); // len2 is usize

    let result_len = if len1 >= len2 { len1 } else { len2 };
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < result_len
        invariant
            result_vec.len() == i,
            i <= result_len,
            forall|j: int| 0 <= j < i ==> {
                if j < len1 as int && j < len2 as int {
                    result_vec[j as usize] as int == c1[j as usize] as int - c2[j as usize] as int
                } else if j < len1 as int && j >= len2 as int {
                    result_vec[j as usize] as int == c1[j as usize] as int
                } else if j >= len1 as int && j < len2 as int {
                    result_vec[j as usize] as int == 0 - c2[j as usize] as int
                } else {
                    result_vec[j as usize] as int == 0
                }
            },
        decreases result_len - i
    {
        let val1 = if i < len1 { c1[i] } else { 0 };
        let val2 = if i < len2 { c2[i] } else { 0 };
        let diff = val1.into() - val2.into();
        result_vec.push(diff);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}