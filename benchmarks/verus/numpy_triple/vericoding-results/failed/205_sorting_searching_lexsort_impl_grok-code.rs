// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Changed quantifier variable types from nat to int in ensures, invariant, and appended 0 <= conditions to index variables for proper int indexing */
fn row_less(keys: &Vec<Vec<i8>>, i: usize, j: usize) -> (result: bool)
    requires
        0 <= i < keys.len(),
        0 <= j < keys.len(),
    ensures
        result == (exists|k: int| 0 <= k && k < keys[i as int]@.len() && keys[i as int]@[k] != keys[j as int]@[k] &&
         (forall|l: int| 0 <= l && l < k ==> keys[i as int]@[l] == keys[j as int]@[l]) ==> keys[i as int]@[k] < keys[j as int]@[k]),
        (!exists|k: int| 0 <= k && k < keys[i as int]@.len() && keys[i as int]@[k] != keys[j as int]@[k]) ==> result == false,
{
    let mut idx = 0;
    let m = keys[i].len();
    while idx < m
        invariant
            0 <= idx <= m,
            forall|l: int| 0 <= l && l < idx ==> keys[i as int]@[l] == keys[j as int]@[l],
    {
        if keys[i][idx] < keys[j][idx] {
            return true;
        } else if keys[i][idx] > keys[j][idx] {
            return false;
        }
        idx += 1;
    }
    false
}

/* helper modified by LLM (iteration 5): Added old() for &mut parameter in requires */
fn swap(indices: &mut Vec<u8>, p: usize, q: usize)
    requires
        0 <= p < old(indices).len(),
        0 <= q < old(indices).len(),
    ensures
        indices@.len() == old(indices)@.len(),
        forall|i: int| 0 <= i < indices.len() && i != p as int && i != q as int ==> #[trigger] indices@[i] == old(indices)@[i],
        indices@[p as int] == old(indices)@[q as int],
        indices@[q as int] == old(indices)@[p as int],
{
    let temp = indices[p];
    indices[p] = indices[q];
    indices[q] = temp;
}
// </vc-helpers>

// <vc-spec>
fn lexsort(keys: Vec<Vec<i8>>) -> (indices: Vec<u8>)
    requires 
        keys.len() > 0,
        keys.len() > 0 ==> keys[0].len() > 0,
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i as int]@.len() == keys[0]@.len(),
    ensures
        indices@.len() == keys[0]@.len(),
        /* indices contains all values from 0 to n-1 exactly once */
        forall|i: int| 0 <= i < keys[0]@.len() ==> #[trigger] indices@.contains(i as u8),
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices[i as int] != indices[j as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Changed quantifier variable types from nat to int in invariants, and appended 0 <= conditions for index variables to fix type mismatches */
{
    let nn = keys.len();
    let mut indices: Vec<u8> = Vec::new();
    for x in 0..nn {
        indices.push(x as u8);
    }
    let mut i = 0;
    while i < nn
        invariant
            indices@.len() == nn as nat,
            forall|k: int| 0 <= k && 0 <= k < indices@.len() ==> indices@[k] < (nn as u8),
            forall|k1: int, k2: int| 0 <= k1 && 0 <= k2 && 0 <= k1 < indices@.len() && 0 <= k2 < indices@.len() && k1 != k2 ==> indices@[k1] != indices@[k2],
    {
        let mut j = 0;
        while j < nn - i - 1
            invariant
                0 <= j <= nn - i - 1,
                indices@.len() == nn as nat,
                forall|k: int| 0 <= k && k < indices@.len() + i ==> (forall|l: int| 0 <= l && k <= l < indices@.len() ==> !row_less(&keys, indices@[l] as usize, indices@[k] as usize)),
        {
            if row_less(&keys, indices[j] as usize, indices[j + 1] as usize) {
                swap(&mut indices, j, j + 1);
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