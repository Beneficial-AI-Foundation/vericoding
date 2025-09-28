// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


fn is_sorted_by_index(keys: &Vec<Vec<i8>>, indices: &Vec<u8>, len: int) -> bool
    requires
        keys@.len() > 0,
        indices@.len() == len,
        len <= keys[0]@.len(),
        forall|i: int| 0 <= i < keys@.len() ==> keys[i]@.len() == keys[0]@.len(),
        forall|k: int| 0 <= k < indices@.len() ==> 0 <= indices@[k] as int < keys[0]@.len()
    ensures
        result ==> (
            forall|i: int, j: int| 0 <= i < j < len ==> {
                let idx_i = indices@[i] as int;
                let idx_j = indices@[j] as int;
                key_comparison(keys, idx_i, idx_j) <= 0
            }
        )
{
    forall(|i: int, j: int| 0 <= i < j < len ==> {
        let idx_i = indices@[i] as int;
        let idx_j = indices@[j] as int;
        key_comparison(keys, idx_i, idx_j) <= 0
    })
}

predicate distinct_values(v: Vec<u8>, count: int) -> bool
    requires 0 <= count <= v@.len()
    ensures result ==> forall|i: int, j: int| 0 <= i < j < count ==> v@[i] != v@[j]
{
    if count <= 1 {
        true
    } else {
        distinct_values(v, count - 1) && 
        forall(|j: int| 0 <= j < count - 1 ==> v@[j] != v@[count - 1])
    }
}

spec fn key_comparison(keys: &Vec<Vec<i8>>, i: int, j: int) -> int
    requires
        0 <= i < keys[0]@.len(),
        0 <= j < keys[0]@.len(),
        keys@.len() > 0,
        forall|k: int| 0 <= k < keys@.len() ==> keys[k]@.len() == keys[0]@.len()
{
    /* helper modified by LLM (iteration 5): fix sequence indexing syntax in parameter type */
    if i == j {
        0
    } else {
        let mut k: int = 0;
        while k < keys@.len()
            invariant 
                0 <= k <= keys@.len(),
                forall|l: int| 0 <= l < k ==> keys@[l][i] == keys@[l][j]
        {
            if keys@[k][i] != keys@[k][j] {
                return if keys@[k][i] < keys@[k][j] { -1 } else { 1 };
            }
            k = k + 1;
        }
        0
    }
}

lemma proof_distinct_implies_permuation(v: Vec<u8>, n: nat)
    requires
        v@.len() == n,
        forall|i: int| 0 <= i < n ==> 0 <= v@[i] as int < n,
        distinct_values(v, n as int)
    ensures
        forall|value: int| 0 <= value < n ==> v@.contains(value as u8)
{
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
{
    /* code modified by LLM (iteration 5): fix compilation error with proper sequence indexing syntax */
    let n = keys[0]@.len() as u8;
    let mut indices = Vec::new();
    let mut i: u8 = 0;
    
    while i < n
        invariant
            i <= n,
            indices@.len() == i as int,
            distinct_values(indices, i as int),
            forall|k: int| 0 <= k < indices@.len() ==> 0 <= indices@[k] as int < n as int,
            is_sorted_by_index(&keys, &indices, i as int)
        decreases (n as int - i as int)
    {
        let pos = find_insert_position(&keys, &indices, i);
        indices.insert(pos, i);
        i = i + 1;
    }
    
    proof {
        proof_distinct_implies_permuation(indices, n as nat);
    }
    
    indices
}

fn find_insert_position(keys: &Vec<Vec<i8>>, sorted: &Vec<u8>, new_val: u8) -> (pos: usize)
    requires
        keys@.len() > 0,
        forall|i: int| 0 <= i < keys@.len() ==> keys[i]@.len() == keys[0]@.len(),
        sorted@.len() >= 0,
        is_sorted_by_index(keys, sorted, sorted@.len()),
        distinct_values(*sorted, sorted@.len()),
        forall|k: int| 0 <= k < sorted@.len() ==> 0 <= sorted@[k] as int < keys[0]@.len(),
        0 <= new_val as int < keys[0]@.len(),
        !sorted@.contains(new_val)
    ensures
        0 <= pos <= sorted@.len(),
        forall|i: int| 0 <= i < pos ==> key_comparison(keys, sorted@[i] as int, new_val as int) <= 0,
        forall|i: int| pos <= i < sorted@.len() ==> key_comparison(keys, new_val as int, sorted@[i] as int) <= 0
{
    let mut pos = 0;
    let mut i = 0;
    
    while i < sorted.len() as u8
        invariant
            0 <= i <= sorted@.len() as u8,
            0 <= pos <= i as int,
            forall|j: int| 0 <= j < pos ==> key_comparison(keys, sorted@[j] as int, new_val as int) <= 0,
            forall|j: int| pos <= j < i as int ==> key_comparison(keys, new_val as int, sorted@[j] as int) > 0
        decreases (sorted@.len() as int - i as int)
    {
        if key_comparison(keys, sorted[i as usize] as int, new_val as int) <= 0 {
            pos = i as int + 1;
        } else {
            // Maintain invariant
        }
        i = i + 1;
    }
    
    pos
}

proof fn proof_distinct_implieds_permutation(indices: &Vec<u8>, n: int)
    requires
        indices@.len() == n,
        n >= 0,
        forall|i: int| 0 <= i < n ==> 0 <= indices@[i] as int < n,
        distinct_values(*indices, n)
    ensures
        forall|value: int| 0 <= value < n ==> indices@.contains(value as u8)
{
}
// </vc-code>


}
fn main() {}