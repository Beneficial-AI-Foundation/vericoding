// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed compilation error by changing loop variable to usize; Corrected next calculation index and assertion to refer to (i-1); assumed no overflow in multiplication */
    let mut result: Vec<i8> = Vec::new();
    result.push(a[0]);
    let mut i: usize = 1;
    while i < a.len()
        invariant
            result.len() as int == i as int,
            result[0] == a[0],
            i as int >= 1,
            i as int <= a.len() as int,
            forall|k: int| 0 < k < i as int ==> result[k] as int == result[k-1] as int * a[k] as int
        decreases a.len() - i
    {
        let prev = result[(i - 1) as usize];
        let curr = a[i as usize];
        let next = (prev as i32 * curr as i32) as i8;
        proof {
            assert(next as int == prev as int * curr as int);
        }
        result.push(next);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}