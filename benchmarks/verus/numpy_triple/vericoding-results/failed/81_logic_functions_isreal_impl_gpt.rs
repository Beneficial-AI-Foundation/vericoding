// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for a complex number being real (imag == 0.0) */
spec fn is_real(c: Complex) -> bool { c.imag == 0.0 }
/* helper modified by LLM (iteration 3): lemma relating == 0.0 and != 0.0 for f64 */
proof fn eq_vs_neq_zero(v: f64) ensures (v == 0.0) == !(v != 0.0) { }
// </vc-helpers>

// <vc-spec>
fn isreal(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].real == x[i].real),
        forall|i: int| 0 <= i < x.len() ==> result[i] == !(x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i].imag == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build boolean result without unsupported reserve_exact; maintain invariants tying out entries to x */
    let mut out: Vec<bool> = Vec::new();
    let n: usize = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            out.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> out@[j] == (x@[j].imag == 0.0),
            forall|j: int| 0 <= j < i ==> out@[j] == !(x@[j].imag != 0.0),
        decreases n - i
    {
        let ci = x[i];
        let b = ci.imag == 0.0;
        out.push(b);
        proof {
            let ii: int = i as int;
            assert(ci == x@[ii]);
            eq_vs_neq_zero(ci.imag);
            assert(b == (x@[ii].imag == 0.0));
            assert(b == !(x@[ii].imag != 0.0));
            assert(out@[ii] == b);
        }
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}