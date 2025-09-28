// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert mathematical int to i8 with bounds */
fn int_to_i8(x: int) -> (result: i8)
    requires
        x >= -128,
        x <= 127,
    ensures
        result as int == x,
{
    let r: i8 = #[verifier::truncate] (x as i8);
    r
}
// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use mathematical int arithmetic and safe cast */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> v@[j] == start as int + j * (step as int),
        decreases n - i
    {
        let idx: int = i as int;
        let val: int = start as int + idx * (step as int);
        let elem: i8 = #[verifier::truncate] (val as i8);
        v.push(elem);
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}