// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn vec_product(shape: Seq<usize>) -> nat
    decreases shape.len()
{
    if shape.len() == 0 {
        1nat
    } else {
        (shape[0] as nat) * vec_product(shape.skip(1))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): product from a start index and proof it's positive */
spec fn prod_from(shape: Seq<usize>, start: nat) -> nat
    decreases shape.len() - start
{
    if start >= shape.len() {
        1nat
    } else {
        (shape[start] as nat) * prod_from(shape, start + 1)
    }
}

proof fn prod_from_nonzero(shape: Seq<usize>, start: nat)
    requires forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
    ensures prod_from(shape, start) > 0,
    decreases shape.len() - start
{
    if start >= shape.len() {
        proof {
            assert(prod_from(shape, start) == 1nat);
            assert(1nat > 0);
        }
    } else {
        prod_from_nonzero(shape, start + 1);
        proof {
            assert(prod_from(shape, start) == (shape[start] as nat) * prod_from(shape, start + 1));
            assert(shape[start] > 0);
            assert(prod_from(shape, start + 1) > 0);
            assert((shape[start] as nat) * prod_from(shape, start + 1) > 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn unravel_index(indices: Vec<usize>, shape: Vec<usize>) -> (result: Vec<Vec<usize>>)
    requires 
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] as nat) < vec_product(shape@),
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == shape.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < shape.len() ==> 
            #[trigger] result[i][j] < shape[j],
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            (indices[i] != indices[j] ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute unravel indices using prod_from helper */
    let mut result: Vec<Vec<usize>> = Vec::new();
    let n: nat = shape@.len();
    let n_int: int = n as int;
    let total: int = indices.len() as int;
    let mut i: int = 0;
    while i < total
        invariant 0 <= i && i <= total;
        invariant result@.len() as int == i;
        invariant forall|p: int| 0 <= p < i ==> #[trigger] (result@[p]@.len() as int == n_int && forall|q: int| 0 <= q < n_int ==> result@[p]@[q] < shape@[q]));
        decreases total - i;
    {
        let idx_nat: nat = indices[i as usize] as nat;
        let mut coords: Vec<usize> = Vec::new();
        let mut j: int = 0;
        while j < n_int
            invariant 0 <= j && j <= n_int;
            invariant coords@.len() as int == j;
            invariant forall|q: int| 0 <= q < j ==> #[trigger] coords@[q] < shape@[q];
            decreases n_int - j;
        {
            let stride: nat = prod_from(shape@, (j + 1) as nat);
            let coord_nat: nat = (idx_nat / stride) % (shape[j as usize] as nat);
            coords.push(coord_nat as usize);
            j += 1;
        }
        result.push(coords);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}