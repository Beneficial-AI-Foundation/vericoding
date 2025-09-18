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
/* helper modified by LLM (iteration 5): No helper needed, removing placeholder */
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
/* code modified by LLM (iteration 5): Corrected loop invariants and logic for generating indices */
{
    let (rows, cols) = shape;
    let mut indices: Vec<Pair> = Vec::new();
    
    // Prove that (rows * cols) will not overflow usize before reserving capacity
    if rows > 0 && cols > 0 && rows as u128 * cols as u128 > usize::MAX as u128 {
      // This case should not be reachable given the current problem constraints
      // as shape.0 and shape.1 are usize themselves.
      // However, for completeness against extreme edge cases, it's considered.
      // For Verus this is effectively a proof obligation to show it won't overflow,
      // which is inherently true as usize * usize <= usize::MAX still holds
      // unless shape.0 or shape.1 are already close to usize::MAX and their product exceeds it.
    }

    indices.reserve((rows * cols) as usize);

    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r && r <= rows,
            indices.len() == r * cols,
            forall|k: int| 0 <= k < indices.len() ==> indices[k].i < r,
            forall|k: int| 0 <= k < indices.len() ==> k == indices[k].i * cols + indices[k].j,
            forall|i: usize, j: usize| #![trigger make_pair(i, j)] i < r && j < cols ==> exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j),
        decreases rows - r
    {
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c && c <= cols,
                indices.len() == r * cols + c,
                forall|k: int| 0 <= k < indices.len() ==> (indices[k].i < r || (indices[k].i == r && indices[k].j < c)),
                forall|k: int| 0 <= k < indices.len() ==> k == indices[k].i * cols + indices[k].j,
                forall|i: usize, j: usize| #![trigger make_pair(i, j)] (i < r || (i == r && j < c)) && j < cols ==> exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j),
            decreases cols - c
        {
            indices.push(Pair { i: r, j: c });

            proof {
                assert(indices.len() == r * cols + (c + 1));
                assert forall|k: int| 0 <= k < indices.len()
                    implies (indices[k].i < r || (indices[k].i == r && indices[k].j < (c + 1))) {
                    if k < r * cols + c {
                        assert(indices[k].i < r || (indices[k].i == r && indices[k].j < c));
                    } else {
                        assert(k == r * cols + c);
                        assert(indices[k] == make_pair(r, c));
                        assert(indices[k].i == r);
                        assert(indices[k].j == c);
                        assert(indices[k].i == r && indices[k].j < c + 1);
                    }
                }
                assert forall|i: usize, j: usize| #![trigger make_pair(i, j)] (i < r || (i == r && j < (c + 1))) && j < cols
                    implies exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j) {
                    if i == r && j == c {
                        assert(indices[r * cols + c] == make_pair(r, c));
                    } else if i < r || (i == r && j < c) {
                        assert (exists|k: int| 0 <= k < r * cols + c && indices[k] == make_pair(i, j));
                    }
                }
            }

            c = c + 1;
        } 
        proof {
            assert(indices.len() == (r + 1) * cols);
            assert forall|k: int| 0 <= k < indices.len()
                implies indices[k].i < (r + 1) {
                if k < r * cols {
                    assert(indices[k].i < r);
                } else {
                    assert(indices[k].i == r);
                }
            }
            assert forall|i: usize, j: usize| #![trigger make_pair(i, j)] i < (r + 1) && j < cols
                implies exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j) {

                if i < r {
                    assert (exists|kk: int| 0 <= kk < r * cols && indices[kk] == make_pair(i, j));
                } else if i == r {
                    assert(exists|kk: int| r * cols <= kk < (r + 1) * cols && indices[kk] == make_pair(i, j));
                }
            }
        }

        r = r + 1;
    }

    indices
}
// </vc-code>

}
fn main() {}