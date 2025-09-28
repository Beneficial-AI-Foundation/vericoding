// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple identity function to aid boolean rewrites in proofs */
fn id_bool(b: bool) -> (result: bool)
    ensures
        result == b,
{
    b
}

// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == (x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag == 0.0 ==> result@[i] == false),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag != 0.0 ==> result@[i] == true),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == false ==> x@[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid moving out of Vec by borrowing; compute boolean directly and maintain invariants */
    let n = x.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x@.len() == n as int,
            (i as int) <= n as int,
            res.len() == i,
            forall|j: int| 0 <= j < res@.len() ==> res@[j] == (x@[j].imag != 0.0),
        decreases (n as int) - (i as int)
    {
        let old_seq = res@;
        let old_len = res.len();
        let val = x[i].imag != 0.0;
        res.push(val);
        proof {
            assert(old_len as int == old_seq.len());
            assert(res@ == old_seq.push(val));
            assert(res@[(old_len as int)] == val);
        }
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}