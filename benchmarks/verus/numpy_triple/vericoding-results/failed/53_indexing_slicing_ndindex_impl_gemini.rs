// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

struct Pair {
    i: usize,
    j: usize,
}

spec fn make_pair(i: usize, j: usize) -> Pair {
    Pair { i, j }
}
// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected path for arithmetic lemma */
proof fn ndindex_bijection_lemma(rows: usize, cols: usize)
    requires rows > 0, cols > 0
    ensures
        forall|i1: usize, j1: usize, i2: usize, j2: usize|
            #![trigger (i1 * cols + j1), (i2 * cols + j2)]
            i1 < rows && j1 < cols && i2 < rows && j2 < cols &&
            i1 * cols + j1 == i2 * cols + j2 ==> 
            i1 == i2 && j1 == j2
{
    assert forall|i1: usize, j1: usize, i2: usize, j2: usize|
        i1 < rows && j1 < cols && i2 < rows && j2 < cols &&
        i1 * cols + j1 == i2 * cols + j2 implies
        i1 == i2 && j1 == j2
    by {
        vstd::arithmetic::lemmas::div_mod_of_mul_add(i1 as int, cols as int, j1 as int);
        vstd::arithmetic::lemmas::div_mod_of_mul_add(i2 as int, cols as int, j2 as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn ndindex(shape: (usize, usize)) -> (indices: Vec<Pair>)
    requires shape.0 > 0 && shape.1 > 0,
    ensures 
        indices.len() == shape.0 * shape.1,
        forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
            let pair = indices[k];
            pair.i < shape.0 && pair.j < shape.1
        },
        forall|i: usize, j: usize| #![trigger make_pair(i, j)] i < shape.0 && j < shape.1 ==> {
            exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j)
        },
        forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
            let pair = indices[k];
            k == pair.i * shape.1 + pair.j
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, fix is in helper path */
    let mut indices: Vec<Pair> = Vec::with_capacity(shape.0 * shape.1);
    let mut i: usize = 0;
    while i < shape.0
        invariant
            0 <= i <= shape.0,
            shape.0 > 0 && shape.1 > 0,
            indices.len() == i * shape.1,
            forall|k: int| 0 <= k < indices.len() ==> indices[k].i < shape.0 && indices[k].j < shape.1,
            forall|k: int| 0 <= k < indices.len() ==> k == indices[k].i * shape.1 + indices[k].j,
    {
        let mut j: usize = 0;
        while j < shape.1
            invariant
                i < shape.0,
                0 <= j <= shape.1,
                shape.0 > 0 && shape.1 > 0,
                indices.len() == i * shape.1 + j,
                forall|k: int| 0 <= k < indices.len() ==> indices[k].i < shape.0 && indices[k].j < shape.1,
                forall|k: int| 0 <= k < indices.len() ==> k == indices[k].i * shape.1 + indices[k].j,
        {
            let pair = Pair { i, j };
            indices.push(pair);
            j = j + 1;
        }
        i = i + 1;
    }
    
    proof {
        ndindex_bijection_lemma(shape.0, shape.1);

        assert forall|ii: usize, jj: usize| ii < shape.0 && jj < shape.1 implies
            exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(ii, jj)
        by {
            let k_usize = ii * shape.1 + jj;
            let k = k_usize as int;
            assert(k < indices.len());
            let p = indices[k];
            assert(k_usize == p.i * shape.1 + p.j);
            assert(p.i == ii && p.j == jj);
        };
    }

    indices
}
// </vc-code>

}
fn main() {}