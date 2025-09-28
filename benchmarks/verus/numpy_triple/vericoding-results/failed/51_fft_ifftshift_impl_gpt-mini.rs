// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec idx_shift for computing shifted index */
spec fn idx_shift(n: int, i: int) -> int
{
    (i + n / 2) % n
}

/* helper modified by LLM (iteration 5): lemma asserting modulo bounds for positive divisor */
proof fn mod_pos_bounds(a: int, b: int)
    requires b > 0,
    ensures
        0 <= a % b,
        a % b < b,
{
    assert(0 <= a % b);
    assert(a % b < b);
}

// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement ifftshift with safe integer arithmetic and maintain invariants */
    let n: usize = x.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            (result@).len() == i as int,
            forall |k: int| 0 <= k < i as int ==> (result@)[k] == (x@)[((k + (n as int) / 2) % (n as int))],
        decreases n - i
    {
        let j_int: int = ((i as int) + (n as int) / 2) % (n as int);
        proof {
            mod_pos_bounds((i as int) + (n as int) / 2, n as int);
            assert(0 <= j_int);
            assert(j_int < n as int);
        }
        let j: usize = j_int as usize;
        result.push(x[j]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}