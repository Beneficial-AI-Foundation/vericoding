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
    /* code modified by LLM (iteration 5): Fixed invariants for nested loops to properly handle existence conditions */
    let mut indices = Vec::new();
    let (rows, cols) = shape;
    
    for i in 0..rows
        invariant
            indices.len() == i * cols,
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair: Pair = indices[k];
                pair.i < rows && pair.j < cols
            },
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair: Pair = indices[k];
                k == pair.i * cols + pair.j
            },
            forall|ii: usize, jj: usize| #![trigger make_pair(ii, jj)] ii < i && jj < cols ==> {
                exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(ii, jj)
            }
    {
        for j in 0..cols
            invariant
                indices.len() == i * cols + j,
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair: Pair = indices[k];
                    pair.i < rows && pair.j < cols
                },
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair: Pair = indices[k];
                    k == pair.i * cols + pair.j
                },
                forall|ii: usize, jj: usize| #![trigger make_pair(ii, jj)] (ii < i && jj < cols) || (ii == i && jj < j) ==> {
                    exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(ii, jj)
                }
        {
            let pair = Pair { i, j };
            indices.push(pair);
        }
    }
    indices
}
// </vc-code>

}
fn main() {}