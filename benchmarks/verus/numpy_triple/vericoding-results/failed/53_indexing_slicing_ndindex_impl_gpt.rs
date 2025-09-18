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
/* helper modified by LLM (iteration 5): arithmetic helpers for row-major indexing */
spec fn linear_index(i: usize, j: usize, cols: usize) -> int { (i as int) * (cols as int) + (j as int) }
/* helper modified by LLM (iteration 5): in-bounds predicate */
spec fn inside(i: usize, j: usize, shape: (usize, usize)) -> bool { i < shape.0 && j < shape.1 }
/* helper modified by LLM (iteration 5): standard Euclidean division facts for usize */
proof fn div_mod_props(k: usize, cols: usize)
    requires cols > 0
    ensures
        k == (k / cols) * cols + (k % cols),
        k % cols < cols
{ }
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
    /* code modified by LLM (iteration 5): row-major enumeration with loop invariants */
    let rows = shape.0;
    let cols = shape.1;
    let total = rows * cols;

    let mut v: Vec<Pair> = Vec::new();
    let mut k: usize = 0;

    while k < total
        invariant
            rows > 0 && cols > 0,
            k <= total,
            v.len() == k,
            forall|mu: usize| mu < k ==> {
                let p = v@[mu as int];
                p == make_pair(mu / cols, mu % cols)
            }
        decreases (total - k)
    {
        let i_k: usize = k / cols;
        let j_k: usize = k % cols;

        proof { div_mod_props(k, cols); }

        let p = make_pair(i_k, j_k);
        v.push(p);
        k = k + 1;
    }

    v
}
// </vc-code>

}
fn main() {}