// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove nested proof block and directly apply forall to get non-zero at index */
proof fn lemma_nonzero_from_forall_exec(x: Vec<i8>, i: int)
    requires
        forall|k: int| 0 <= k < x.len() ==> x[k] != 0i8,
        0 <= i < x.len(),
    ensures
        x[i] != 0i8,
{
    assert(0 <= i < x.len());
    assert(x[i] != 0i8);
}

// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): element-wise modulo loop; removed nested proof block causing compile error */
    let n = x1.len();
    let mut out: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
            x1.len() == n,
            x2.len() == n,
            forall|k: int| 0 <= k < (n as int) ==> x2[k] != 0i8,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] out[k] == x1[k] % x2[k],
        decreases ((n as int) - (i as int))
    {
        assert(i < x1.len());
        assert(i < x2.len());
        assert(0 <= (i as int) && (i as int) < (n as int));
        assert(x2[i as int] != 0i8);
        let a = x1[i];
        let b = x2[i];
        assert(b != 0i8);
        let r = a % b;
        out.push(r);
        i = i + 1;
    }
    out
}
// </vc-code>


}
fn main() {}