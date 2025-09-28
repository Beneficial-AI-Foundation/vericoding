// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int - c2[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result[j] == c1[j]
                } else if j >= c1.len() && j < c2.len() {
                    result[j] as int == 0 - c2[j] as int
                } else {
                    result[j] == 0
                }
            },
        decreases max_len - i
    {
        let val: i8 = if i < c1.len() && i < c2.len() {
            c1[i] - c2[i]
        } else if i < c1.len() && i >= c2.len() {
            c1[i]
        } else if i >= c1.len() && i < c2.len() {
            0 - c2[i]
        } else {
            0
        };
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}