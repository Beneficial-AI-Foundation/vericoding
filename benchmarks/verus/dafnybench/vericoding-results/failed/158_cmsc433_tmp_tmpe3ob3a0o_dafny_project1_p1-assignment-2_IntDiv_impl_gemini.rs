// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bit_vector assertion to prove no underflow */
fn euclid_div_neg(m: i32, n: i32) -> (ret: (i32, i32))
    requires
        m < 0,
        n > 0,
    ensures
        m == n * ret.0 + ret.1,
        0 <= ret.1 < n,
{
    let q_trunc = m / n;
    let r_trunc = m % n;
    if r_trunc < 0 {
        assert(q_trunc > i32::MIN) by(bit_vector);
        (q_trunc - 1, r_trunc + n)
    } else {
        (q_trunc, r_trunc)
    }
}
// </vc-helpers>

// <vc-spec>
fn IntDiv(m: i32, n: i32) -> (ret: (i32, i32))
    requires n > 0
    ensures m == n * ret.0 + ret.1 && 0 <= ret.1 < n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): logic unchanged, correctness depends on fixed helper */
    if m >= 0 {
        (m / n, m % n)
    } else {
        euclid_div_neg(m, n)
    }
}
// </vc-code>

}
fn main() {}