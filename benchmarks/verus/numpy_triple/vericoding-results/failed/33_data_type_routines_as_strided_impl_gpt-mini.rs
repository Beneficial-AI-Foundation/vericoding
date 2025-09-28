// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that i*stride is within x bounds */
proof fn index_within_bounds(i: int, stride: usize, m: usize, x: &Vec<f32>)
    requires
        0 <= i,
        i < m as int,
        stride > 0,
        m * stride <= x@.len(),
    ensures
        0 <= i * (stride as int),
        i * (stride as int) < x@.len() as int,
{
    assert(0 <= i);
    assert((stride as int) > 0);

    // (m - i) > 0 because i < m
    assert((m as int) - i > 0);
    // multiply positive quantities to get positive difference
    assert(((m as int) - i) * (stride as int) > 0);
    // expand to get m*stride - i*stride > 0
    assert((m as int) * (stride as int) - i * (stride as int) > 0);
    // conclude i*stride < m*stride
    assert(i * (stride as int) < (m as int) * (stride as int));

    // relate to m*stride as int and x length
    assert((m as int) * (stride as int) == (m * stride) as int);
    assert((m * stride) as int <= x@.len() as int);

    assert(i * (stride as int) < x@.len() as int);
    assert(0 <= i * (stride as int));
}

// </vc-helpers>

// <vc-spec>
fn numpy_as_strided(x: &Vec<f32>, stride: usize, m: usize) -> (result: Vec<f32>)
    requires 
        stride > 0,
        m * stride <= x@.len(),
    ensures
        result@.len() == m,
        forall|i: int| 0 <= i < m ==> result@[i] == x@[i * stride as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement as_strided without using spec ints in executable code */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            result@.len() == i as nat,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == x@[j * (stride as int)],
        decreases
            m - i
    {
        proof {
            // prove index is within bounds using the helper (spec-level reasoning)
            index_within_bounds(i as int, stride, m, x);
            assert((i as int) * (stride as int) < x@.len() as int);
        }
        let idx: usize = i * stride;
        let v: f32 = x[idx];
        result.push(v);
        i = i + 1;
    }

    result
}

// </vc-code>

}
fn main() {}