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
fn compute_index(i: usize, j: usize, cols: usize) -> usize { i * cols + j }

proof fn index_unique(i1: usize, i2: usize, j1: usize, j2: usize, cols: usize)
    requires i1 < cols, i2 < cols,
    ensures i1 * cols + j1 == i2 * cols + j2 ==> i1 == i2 && j1 == j2
{
}

proof fn index_within_range(i: usize, j: usize, rows: usize, cols: usize) -> (idx: usize)
    requires i < rows, j < cols,
    ensures 0 <= idx < rows * cols
{
}

spec fn valid_coordinates(i: usize, j: usize, rows: usize, cols: usize) -> bool {
    i < rows && j < cols
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
    let rows = shape.0;
    let cols = shape.1;
    let mut indices = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            indices.len() == i * cols,
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair = indices[k];
                pair.i < rows && pair.j < cols
            },
            forall|ii: usize, jj: usize| #![trigger make_pair(ii, jj)] ii < i && jj < cols ==> {
                exists|kk: int| 0 <= kk < indices.len() && indices[kk] == make_pair(ii, jj)
            },
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair = indices[k];
                k == pair.i * cols + pair.j
            }
    {
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                indices.len() == i * cols + j,
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair = indices[k];
                    pair.i <= i && (pair.i == i ==> pair.j < j) && pair.j < cols
                },
                forall|ii: usize, jj: usize| #![trigger make_pair(ii, jj)] {
                    (ii < i && jj < cols) || (ii == i && jj < j)
                } ==> {
                    exists|kk: int| 0 <= kk < indices.len() && indices[kk] == make_pair(ii, jj)
                },
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair = indices[k];
                    k == pair.i * cols + pair.j
                }
        {
            let idx = compute_index(i, j, cols);
            proof {
                index_within_range(i, j, rows, cols);
            }
            indices.push(make_pair(i, j));
            proof {
                assert(indices[idx] == make_pair(i, j)) by {
                    assert(idx == indices.len() - 1);
                };
            }
            j += 1;
        }
        i += 1;
    }
    indices
}
// </vc-code>

}
fn main() {}