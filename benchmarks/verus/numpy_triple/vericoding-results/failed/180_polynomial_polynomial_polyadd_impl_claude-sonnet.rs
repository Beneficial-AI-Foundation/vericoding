// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function to safely add i8 values */
fn safe_add_i8(a: i8, b: i8) -> (result: i8)
    requires
        -128 <= a as int + b as int <= 127,
    ensures
        result as int == a as int + b as int,
{
    a + b
}
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
{
    /* code modified by LLM (iteration 5): fixed if-else expression syntax with proper comma placement */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result[j] as int == c1[j] as int
                } else if j >= c1.len() && j < c2.len() {
                    result[j] as int == c2[j] as int
                } else {
                    result[j] as int == 0
                }
            },
        decreases max_len - i
    {
        let val = if i < c1.len() && i < c2.len() {
            proof {
                assert(-128 <= c1[i] as int <= 127);
                assert(-128 <= c2[i] as int <= 127);
                assert(-256 <= c1[i] as int + c2[i] as int <= 254);
            }
            if c1[i] as int + c2[i] as int > 127 {
                127i8
            } else if c1[i] as int + c2[i] as int < -128 {
                -128i8
            } else {
                safe_add_i8(c1[i], c2[i])
            }
        } else if i < c1.len() && i >= c2.len() {
            c1[i]
        } else if i >= c1.len() && i < c2.len() {
            c2[i]
        } else {
            0
        };
        
        result.push(val);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}