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
/* helper modified by LLM (iteration 5): prove product bound i*cols + j < rows*cols */
proof fn mul_add_lt(rows: usize, cols: usize, i: usize, j: usize)
    requires rows > 0 && cols > 0 && i < rows && j < cols,
    ensures i * cols + j < rows * cols {
    proof {
        // i < rows implies i + 1 <= rows
        assert(i + 1 <= rows);
        // multiply both sides by positive cols
        assert((i + 1) * cols <= rows * cols);
        // j < cols implies j <= cols - 1
        assert(j + 1 <= cols);
        assert(j <= cols - 1);
        // therefore i*cols + j < (i+1)*cols
        assert(i * cols + j < (i + 1) * cols);
        // and (i+1)*cols <= rows*cols, so i*cols + j < rows*cols
        assert(i * cols + j < rows * cols);
    }
}

/* helper modified by LLM (iteration 5): decompose index k into row/col and prove bounds and equality */
proof fn div_mod_decomp(k: usize, rows: usize, cols: usize)
    requires rows > 0 && cols > 0 && k < rows * cols,
    ensures k / cols < rows && k % cols < cols && k == (k / cols) * cols + (k % cols) {
    proof {
        let i = k / cols;
        let j = k % cols;
        // standard division/modulo identity
        assert(k == i * cols + j);
        // modulo bound
        assert(j < cols);
        // from k < rows*cols and k == i*cols + j we get i*cols + j < rows*cols
        assert(i * cols + j < rows * cols);
        // hence i*cols < rows*cols, and since cols > 0 we conclude i < rows
        assert(i * cols < rows * cols);
        assert(i < rows);
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
/* code modified by LLM (iteration 5): generate row-major indices with correct invariants and use Pair literals */
{
    let (rows, cols) = shape;
    let mut indices: Vec<Pair> = Vec::new();
    let mut k: usize = 0;
    while k < rows * cols
        invariant k <= rows * cols,
        invariant indices.len() == k,
        invariant forall|t: usize| t < k ==> {
            let pair = indices[t];
            pair.i < rows && pair.j < cols && t == pair.i * cols + pair.j
        },
        decreases rows * cols - k
    {
        let i = k / cols;
        let j = k % cols;
        proof {
            div_mod_decomp(k, rows, cols);
            assert(i < rows);
            assert(j < cols);
            mul_add_lt(rows, cols, i, j);
            assert(k == i * cols + j);
        }
        indices.push(Pair { i, j });
        k = k + 1;
    }
    indices
}

// </vc-code>

}
fn main() {}