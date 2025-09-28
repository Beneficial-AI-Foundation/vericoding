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
/* code modified by LLM (iteration 5): [replaced unreachable!() with Verus-compatible assert(false)] */
{
    let n1 = c1.len();
    let n2 = c2.len();
    let n = if n1 >= n2 { n1 } else { n2 };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            n == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            forall|j: int| 0 <= j < i as int ==> {
                let c1_val = if j < c1.len() { c1[j] } else { 0i8 };
                let c2_val = if j < c2.len() { c2[j] } else { 0i8 };
                result[j] as int == c1_val as int - c2_val as int
            },
        decreases n - i
    {
        let v1 = if i < n1 { c1[i] } else { 0i8 };
        let v2 = if i < n2 { c2[i] } else { 0i8 };
        
        let d = (v1 as i16) - (v2 as i16);

        if (i8::MIN as i16) <= d && d <= (i8::MAX as i16) {
            result.push(d as i8);
        } else {
            assert(false);
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}