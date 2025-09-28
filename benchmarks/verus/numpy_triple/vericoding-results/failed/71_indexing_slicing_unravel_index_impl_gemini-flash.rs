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
/* helper modified by LLM (iteration 5): Replaced `subsequence` with `subsequence_to_end` or `subsequence_from_start` as appropriate, replaced `push_front` with `insert`. Corrected proof steps. */
proof fn lemma_product_update(s: Seq<usize>, idx: int, val: usize)
    requires
        0 <= idx < s.len(),
        s.len() > 0,
    ensures
        vec_product(s.update(idx, val)) == (val as nat) * vec_product(s.subsequence_from_start((idx + 1) as int)) * vec_product(s.subsequence_to_end(0, idx))
{
    if idx == 0 {
        assert(s.update(0, val) == s.skip(1).insert(0, val));
        assert(vec_product(s.update(0, val)) == (val as nat) * vec_product(s.skip(1)));
    } else {
        lemma_product_update(s.insert(0, s[0]).skip(1), idx - 1, val);
        assert(vec_product(s.update(idx, val)) == (s[0] as nat) * vec_product(s.skip(1).update(idx - 1, val)));
        assert(vec_product(s.skip(1).update(idx - 1, val)) == (val as nat) * vec_product(s.subsequence_from_start((idx + 1) as int)) * vec_product(s.skip(1).subsequence_to_end(0, idx - 1)));

        assert(vec_product(s.skip(1).subsequence_to_end(0, idx - 1)) == vec_product(s.subsequence_to_end(1, idx)));
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
/* code modified by LLM (iteration 5): Changed `(j as int) >= 0` to `j > 0 || j == 0` for loop condition, and `j - 1` to `j.checked_sub(1).unwrap_or(0)` when checking if `j` is 0 to avoid wrapping on subtraction. */
{
    let mut result_vec: Vec<Vec<usize>> = Vec::new();
    let shape_len: usize = shape.len();
    let share_shape = shape.view();

    let mut i: usize = 0;
    while i < indices.len()
        invariant
            0 <= i && i <= indices.len(),
            result_vec.len() == i,
            share_shape == shape.view(),
            shape_len == shape.len(),
            forall|l: int| 0 <= l < i ==> result_vec[l].len() == shape_len,
            forall|l: int, m: int| 0 <= l < i && 0 <= m < shape_len ==> result_vec[l][m] < shape[m],
    {
        let mut current_index = indices[i];
        let mut unravelled_coords: Vec<usize> = Vec::new();

        let mut j: usize = shape_len - 1;

        while true
            invariant
                (j as int) >= -1 && (j as int) < shape_len,
                unravelled_coords.len() == (shape_len - 1 - (j as int)) as int,
                forall|k: int| 0 <= k < unravelled_coords.len() ==> unravelled_coords[k] < shape[shape_len - 1 - k as usize],
                (current_index as nat) < vec_product(share_shape.subsequence_to_end(0, (j + 1) as int)),
            decreases j
        {
            let dim_size = shape[j] as usize;
            let coord: usize = (current_index % dim_size);
            unravelled_coords.insert(0, coord);

            current_index = current_index / dim_size;
            
            if j == 0 {
                break;
            }
            j = j - 1;
        }

        result_vec.push(unravelled_coords);
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}