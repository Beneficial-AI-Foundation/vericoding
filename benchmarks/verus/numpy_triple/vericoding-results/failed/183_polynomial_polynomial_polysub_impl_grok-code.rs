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
    /* code modified by LLM (iteration 3): fixed else branch to conditionally subtract c2[i] only when i < c2.len(), else push 0 */
    let len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result@[j] as int == c1@[j] as int - c2@[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result@[j] as int == c1@[j] as int
                } else if j >= c1.len() && j < c2.len() {
                    result@[j] as int == 0 - c2@[j] as int
                } else {
                    result@[j] == 0
                }
            }
        decreases len - i
    {
        if i < c1.len() && i < c2.len() {
            let val = (c1[i] as i16 - c2[i] as i16) as i8;
            result.push(val);
        } else if i < c1.len() {
            result.push(c1[i]);
        } else {
            if i < c2.len() {
                let val = (0i16 - c2[i] as i16) as i8;
                result.push(val);
            } else {
                result.push(0);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}