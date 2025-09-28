// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): arithmetic lemma for diagonal index bounds without using undefined tokens */
proof fn lemma_diag_index_in_bounds(i: int, n: int)
    requires
        0 <= i,
        0 < n,
        i < n,
    ensures
        0 <= i * n + i,
        i * n + i < n * n,
{
    assert(0 <= i * n) by (nonlinear_arith);
    assert(0 <= i * n + i) by (nonlinear_arith);
    assert(i + i * n < n + i * n) by (nonlinear_arith);
    assert(i * n + i < i * n + n) by (nonlinear_arith);
    assert(i * n + n == (i + 1) * n) by (nonlinear_arith);
    assert(i + 1 <= n) by (nonlinear_arith);
    assert((i + 1) * n <= n * n) by (nonlinear_arith);
    assert(i * n + i < n * n) by (nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn diag(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        matrix.len() == n * n,
        n > 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n as int ==> result@[i] == matrix@[i * n as int + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize loop index, provide proof-casts to int for bounds, and maintain invariant for diagonal values */
    let mut res: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            res.len() == k,
            matrix.len() == n * n,
            forall|j: int| 0 <= j < k as int ==> res@[j] == matrix@[j * n as int + j],
        decreases n - k
    {
        let idx: usize = k * n + k;

        proof {
            let ghost ii: int = k as int;
            let ghost nn: int = n as int;
            lemma_diag_index_in_bounds(ii, nn);
            assert(idx as int == ii * nn + ii) by (nonlinear_arith);
            assert((n * n) as int == nn * nn) by (nonlinear_arith);
            assert(0 <= ii * nn + ii) by (nonlinear_arith);
            assert(ii * nn + ii < nn * nn) by (nonlinear_arith);
            assert(idx < n * n);
        }
        let val: f32 = matrix[idx];

        let ghost old_seq = res@;
        let old_len: usize = res.len();

        res.push(val);

        assert forall|j: int| 0 <= j < k as int ==> res@[j] == matrix@[j * n as int + j] by {
            assert(0 <= j < old_len as int);
            assert(res@[j] == old_seq[j]);
            assert(old_seq[j] == matrix@[j * n as int + j]);
        };

        assert forall|j: int| 0 <= j < (k + 1) as int ==> res@[j] == matrix@[j * n as int + j] by {
            if j < k as int {
                assert(0 <= j < old_len as int);
                assert(res@[j] == old_seq[j]);
                assert(old_seq[j] == matrix@[j * n as int + j]);
            } else {
                assert(j == k as int);
                assert(old_len == k);
                assert(res@[j] == res@[old_len as int]);
                assert(res@[old_len as int] == val);

                let ghost ii: int = k as int;
                let ghost nn: int = n as int;
                assert(j * n as int + j == ii * nn + ii) by (nonlinear_arith);
                assert((k * n + k) as int == ii * nn + ii) by (nonlinear_arith);
                assert(matrix@[j * n as int + j] == matrix@[(k * n + k) as int]);
                assert(matrix@[(k * n + k) as int] == matrix[k * n + k]);
            }
        };

        k = k + 1;
    }
    res
}
// </vc-code>

}
fn main() {}