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
/* helper modified by LLM (iteration 5): coords_to_nat spec */
spec fn coords_to_nat(seq: Seq<usize>, shape: Seq<usize>) -> nat
    requires
        seq.len() == shape.len(),
    decreases seq.len()
{
    if seq.len() == 0 {
        0nat
    } else {
        (seq[0] as nat) * vec_product(shape.skip(1)) + coords_to_nat(seq.skip(1), shape.skip(1))
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
            (indices[i] != indices[j] ==> result[i]@ != result[j]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement unravel_index with proper casts for spec calls and int proof counters */
{
    let n = shape.len();
    let mut result: Vec<Vec<usize>> = Vec::new();

    let mut i = 0usize;
    while i < indices.len()
        invariant
            result.len() == i,
        decreases indices.len() - i
    {
        let idx = indices[i];
        let mut rem: usize = idx;
        let mut coords: Vec<usize> = Vec::new();
        let mut acc: usize = 0;

        let mut j = 0usize;
        while j < n
            invariant
                coords.len() == j,
                (indices[i] as nat) == (acc as nat) * vec_product(shape@.skip(j as int)) + (rem as nat),
                (rem as nat) < vec_product(shape@.skip(j as int)),
            decreases n - j
        {
            let mut suffix_usize = 1usize;
            let mut k = j + 1usize;
            while k < n
                invariant
                    k <= n,
                decreases n - k
            {
                suffix_usize = suffix_usize * shape[k];
                k += 1;
            }

            let coord = rem / suffix_usize;
            coords.push(coord);
            acc = acc * shape[j] + coord;
            rem = rem % suffix_usize;
            j += 1;
        }

        proof {
            assert((rem as nat) < vec_product(shape@.skip(n as int)));
            assert(vec_product(shape@.skip(n as int)) == 1nat);
            assert((rem as nat) == 0nat);
            assert((indices[i] as nat) == (acc as nat));
            assert(coords_to_nat(coords@, shape@) == (indices[i] as nat));
        }

        result.push(coords);

        i += 1;
    }

    proof {
        let m = indices.len() as int;
        let mut a: int = 0;
        while a < m
            invariant
                0 <= a,
                a <= m,
            decreases m - a
        {
            let mut b: int = a + 1;
            while b < m
                invariant
                    a < m,
                decreases m - b
            {
                if indices[a as usize] != indices[b as usize] {
                    if result[a as usize]@ == result[b as usize]@ {
                        assert(coords_to_nat(result[a as usize]@, shape@) == (indices[a as usize] as nat));
                        assert(coords_to_nat(result[b as usize]@, shape@) == (indices[b as usize] as nat));
                        assert(coords_to_nat(result[a as usize]@, shape@) == coords_to_nat(result[b as usize]@, shape@));
                        assert((indices[a as usize] as nat) == (indices[b as usize] as nat));
                        assert(indices[a as usize] == indices[b as usize]);
                    }
                }
                b = b + 1;
            }
            a = a + 1;
        }
    }

    result
}

// </vc-code>

}
fn main() {}