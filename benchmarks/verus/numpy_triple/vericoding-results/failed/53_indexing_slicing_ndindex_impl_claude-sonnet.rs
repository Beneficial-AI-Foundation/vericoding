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
spec fn pair_to_index(pair: Pair, shape: (usize, usize)) -> int {
    pair.i * shape.1 + pair.j
}

spec fn index_to_pair(k: int, shape: (usize, usize)) -> Pair {
    Pair { i: (k / (shape.1 as int)) as usize, j: (k % (shape.1 as int)) as usize }
}

/* helper modified by LLM (iteration 5): fixed type casting issues in division and modulo operations */
proof fn lemma_index_bijection(k: int, shape: (usize, usize))
    requires shape.0 > 0 && shape.1 > 0 && 0 <= k < shape.0 * shape.1
    ensures ({
        let pair = index_to_pair(k, shape);
        &&& pair.i < shape.0
        &&& pair.j < shape.1
        &&& pair_to_index(pair, shape) == k
    })
{
    let pair = index_to_pair(k, shape);
    assert(pair.i == (k / (shape.1 as int)) as usize);
    assert(pair.j == (k % (shape.1 as int)) as usize);
    assert(pair_to_index(pair, shape) == pair.i * shape.1 + pair.j);
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
/* code modified by LLM (iteration 5): fixed type annotations and implementation */
{
    let mut indices = Vec::new();
    let mut i = 0;
    
    while i < shape.0
        invariant
            i <= shape.0,
            indices.len() == i * shape.1,
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair: Pair = indices[k];
                pair.i < shape.0 && pair.j < shape.1
            },
            forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                let pair: Pair = indices[k];
                k == pair.i * shape.1 + pair.j
            }
    {
        let mut j = 0;
        
        while j < shape.1
            invariant
                i < shape.0,
                j <= shape.1,
                indices.len() == i * shape.1 + j,
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair: Pair = indices[k];
                    pair.i < shape.0 && pair.j < shape.1
                },
                forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() ==> {
                    let pair: Pair = indices[k];
                    k == pair.i * shape.1 + pair.j
                }
        {
            let pair = Pair { i, j };
            indices.push(pair);
            j += 1;
        }
        
        i += 1;
    }
    
    proof {
        assert(indices.len() == shape.0 * shape.1);
        
        assert forall|k: int| #![trigger indices[k]] 0 <= k < indices.len() implies {
            let pair: Pair = indices[k];
            pair.i < shape.0 && pair.j < shape.1
        } by {}
        
        assert forall|i: usize, j: usize| #![trigger make_pair(i, j)] i < shape.0 && j < shape.1 implies {
            exists|k: int| 0 <= k < indices.len() && indices[k] == make_pair(i, j)
        } by {
            if i < shape.0 && j < shape.1 {
                let k = i * shape.1 + j;
                assert(0 <= k < indices.len());
                assert(indices[k] == make_pair(i, j));
            }
        }
    }
    
    indices
}
// </vc-code>

}
fn main() {}