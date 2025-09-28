// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove division-multiplication relationship for usize when divisible */
proof fn lemma_div_mul_usize(a: usize, b: usize)
    requires
        b > 0,
        a % b == 0,
    ensures
        (a / b) * b == a,
{
    assert(a == (a / b) * b + (a % b));
    assert(a % b == 0);
    assert((a / b) * b + 0 == (a / b) * b);
    assert(a == (a / b) * b);
}

/* helper modified by LLM (iteration 5): show computed index is within array bounds for dsplit */
proof fn lemma_idx_in_bounds(arr_len: usize, sections: usize, outer: usize, inner: usize)
    requires
        sections > 0,
        arr_len % sections == 0,
        outer < sections,
        inner < arr_len / sections,
    ensures
        outer * (arr_len / sections) + inner < arr_len,
{
    let q: usize = arr_len / sections;
    lemma_div_mul_usize(arr_len, sections);
    assert(q * sections == arr_len);

    // From inner < q and inner being usize, it follows q > 0
    assert(q > 0);

    assert(inner < q);
    assert(outer * q + inner < outer * q + q);
    assert(outer * q + q == (outer + 1) * q);

    assert(outer + 1 <= sections);
    assert((outer + 1) * q <= sections * q);

    assert(outer * q + inner < sections * q);
    assert(sections * q == q * sections);
    assert(outer * (arr_len / sections) + inner < arr_len);
}
// </vc-helpers>

// <vc-spec>
fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): wrap lemma call in proof block for bounds; implement splitting */
    let chunk_size: usize = arr.len() / sections;
    let ghost chunk_size_i: int = chunk_size as int;

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut outer: usize = 0usize;
    while outer < sections
        invariant
            sections > 0,
            arr.len() % sections == 0,
            result.len() == outer,
            outer <= sections,
            forall|i: int| 0 <= i < outer as int ==> result[i].len() == chunk_size,
            forall|i: int, j: int| 0 <= i < outer as int && 0 <= j < chunk_size_i ==> result[i][j] == arr[(i * chunk_size_i) + j],
        decreases sections - outer
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut inner: usize = 0usize;
        while inner < chunk_size
            invariant
                sections > 0,
                arr.len() % sections == 0,
                result.len() == outer,
                chunk.len() == inner,
                inner <= chunk_size,
                outer < sections,
                forall|j: int| 0 <= j < inner as int ==> chunk[j] == arr[((outer as int) * chunk_size_i) + j],
            decreases chunk_size - inner
        {
            let idx: usize = outer * chunk_size + inner;
            proof { lemma_idx_in_bounds(arr.len(), sections, outer, inner); }
            chunk.push(arr[idx]);
            inner += 1;
        }
        assert(chunk.len() == chunk_size);
        assert(forall|j: int| 0 <= j < chunk_size_i ==> chunk[j] == arr[((outer as int) * chunk_size_i) + j]);

        let saved_chunk: Vec<f32> = chunk.clone();
        assert(saved_chunk.len() == chunk_size);
        assert(forall|j: int| 0 <= j < chunk_size_i ==> saved_chunk[j] == chunk[j]);

        let old_len: usize = result.len();
        result.push(saved_chunk);
        assert(result.len() == old_len + 1);
        assert(old_len == outer);
        assert(result[outer as int].len() == chunk_size);
        assert(forall|j: int| 0 <= j < chunk_size_i ==> result[outer as int][j] == result[outer as int][j]);
        assert(forall|j: int| 0 <= j < chunk_size_i ==> result[outer as int][j] == chunk[j]);
        assert(forall|j: int| 0 <= j < chunk_size_i ==> result[outer as int][j] == arr[((outer as int) * chunk_size_i) + j]);

        outer += 1;
    }
    result
}
// </vc-code>

}
fn main() {}