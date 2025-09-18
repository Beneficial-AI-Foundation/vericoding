// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ensure j*stride is within x length using int arithmetic */
proof fn index_mul_lt_len(stride: usize, m: usize, x_len: usize, j: int)
    requires
        stride > 0,
        m * stride <= x_len,
        0 <= j,
        j < (m as int),
    ensures
        j * (stride as int) < (x_len as int)
{
    proof {
        assert(j < m as int);
        assert(j >= 0);
        assert(j <= (m as int) - 1);
        assert(j * (stride as int) <= (((m as int) - 1) * (stride as int)));
        assert((((m as int) - 1) * (stride as int)) < ((m * stride) as int));
        assert((m * stride) as int <= x_len as int);
        assert(j * (stride as int) < x_len as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_as_strided(x: &Vec<f32>, stride: usize, m: usize) -> (result: Vec<f32>)
    requires 
        stride > 0,
        m * stride <= x.len(),
    ensures
        result.len() == m,
        forall|i: int| 0 <= i < m ==> result[i] == x[i * stride],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build the result vector by taking every stride-th element from x, using spec-indexing for proofs */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant i <= m,
                  result.len() == i,
                  forall|j: int| 0 <= j && j < (i as int) ==> result[j as usize] == x@[(j * (stride as int))],
        decreases m - i
    {
        proof {
            assert(result.len() == i);
            index_mul_lt_len(stride, m, x.len(), i as int);
            assert((i as int) * (stride as int) < x.len() as int);
            assert((i * stride) < x.len());
        }
        let val: f32 = x[i * stride];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}