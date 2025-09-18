// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate for nonzero imaginary part */
spec fn is_nonzero_imag(c: Complex) -> bool { c.imag != 0.0 }

/* helper modified by LLM (iteration 5): lemma to extend prefix property after push with int indexing */
proof fn lemma_extend_prefix_property(x: &Vec<Complex>, res: &Vec<bool>, k: usize)
    requires
        forall|j: int| 0 <= j < k as int ==> res[j] == (x[j].imag != 0.0),
        res.len() == k + 1,
        res[k as int] == (x[k as int].imag != 0.0),
    ensures
        forall|j: int| 0 <= j < (k + 1) as int ==> res[j] == (x[j].imag != 0.0)
{ }
// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index types in proofs and maintained invariants */
    let n = x.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            (i as int) <= (x.len() as int),
            forall|j: int| 0 <= j < res.len() as int ==> res[j] == (x[j].imag != 0.0)
        decreases n as int - i as int
    {
        let old_len = res.len();
        assert(old_len == i);
        let b: bool = x[i].imag != 0.0;
        res.push(b);
        assert(res.len() == old_len + 1);
        proof {
            assert(res[old_len as int] == b);
            assert(b == (x[old_len as int].imag != 0.0));
        }
        i += 1;
        assert(res.len() == i);
        proof {
            lemma_extend_prefix_property(x, &res, old_len);
        }
    }
    proof {
        assert(res.len() == n);
        assert(n == x.len());
        assert((res.len() as int) == (x.len() as int));
    }
    res
}
// </vc-code>

}
fn main() {}