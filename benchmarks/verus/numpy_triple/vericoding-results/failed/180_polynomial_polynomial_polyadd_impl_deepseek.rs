// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): keep spec function with proper verification */
spec fn polyadd_spec(c1: Vec<i8>, c2: Vec<i8>, i: int) -> int
{
    if i < c1.len() && i < c2.len() {
        c1[i] as int + c2[i] as int
    } else if i < c1.len() && i >= c2.len() {
        c1[i] as int
    } else if i >= c1.len() && i < c2.len() {
        c2[i] as int
    } else {
        0
    }
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
/* code modified by LLM (iteration 5): add decreases clause to while loop */
{
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;

    while i < max_len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == polyadd_spec(c1, c2, j),
        decreases max_len - i,
    {
        let elem: i8;
        if i < c1.len() && i < c2.len() {
            elem = (c1[i] + c2[i]) as i8;
        } else if i < c1.len() && i >= c2.len() {
            elem = c1[i];
        } else {
            elem = c2[i];
        }
        result.push(elem);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}