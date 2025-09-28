// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn compare_keys(keys: &Vec<Vec<i8>>, a: usize, b: usize, pos: usize) -> (result: i8)
    requires
        a < keys[0]@.len(),
        b < keys[0]@.len(),
        pos < keys.len(),
        keys.len() > 0,
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i as int]@.len() == keys[0]@.len(),
    ensures
        result == -1 || result == 0 || result == 1,
{
    if keys[pos][a] < keys[pos][b] {
        -1
    } else if keys[pos][a] > keys[pos][b] {
        1
    } else {
        0
    }
}

fn lexicographic_compare(keys: &Vec<Vec<i8>>, a: usize, b: usize) -> (result: bool)
    requires
        a < keys[0]@.len(),
        b < keys[0]@.len(),
        keys.len() > 0,
        keys[0].len() > 0,
        forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i as int]@.len() == keys[0]@.len(),
    ensures
        result == true || result == false,
{
    let mut pos = 0;
    while pos < keys.len()
        invariant
            pos <= keys.len(),
            a < keys[0]@.len(),
            b < keys[0]@.len(),
            keys.len() > 0,
            forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i as int]@.len() == keys[0]@.len(),
        decreases keys.len() - pos
    {
        let cmp = compare_keys(keys, a, b, pos);
        if cmp < 0 {
            return true;
        } else if cmp > 0 {
            return false;
        }
        pos += 1;
    }
    a < b
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
    /* code modified by LLM (iteration 5): fixed precondition bounds and invariants for proper verification */
    let n = keys[0].len();
    let mut indices: Vec<u8> = Vec::new();
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices[j] == #[verifier::truncate] j as u8,
        decreases n - i
    {
        indices.push(#[verifier::truncate] i as u8);
        i += 1;
    }
    
    proof {
        assert(indices@.len() == n);
        assert(forall|k: int| 0 <= k < n ==> indices@.contains(#[verifier::truncate] k as u8));
    }
    
    let mut pass = 0;
    while pass < n
        invariant
            pass <= n,
            indices@.len() == n,
            forall|i: int| 0 <= i < n ==> #[trigger] indices@.contains(#[verifier::truncate] i as u8),
            forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices[i as int] != indices[j as int],
        decreases n - pass
    {
        let mut j = 0;
        while j < n - 1
            invariant
                j <= n - 1,
                indices@.len() == n,
                forall|i: int| 0 <= i < n ==> #[trigger] indices@.contains(#[verifier::truncate] i as u8),
                forall|i: int, k: int| 0 <= i < indices@.len() && 0 <= k < indices@.len() && i != k ==> indices[i as int] != indices[k as int],
            decreases n - 1 - j
        {
            if indices[j + 1] as usize < keys[0]@.len() && indices[j] as usize < keys[0]@.len() {
                if lexicographic_compare(&keys, indices[j + 1] as usize, indices[j] as usize) {
                    let temp = indices[j];
                    indices.set(j, indices[j + 1]);
                    indices.set(j + 1, temp);
                }
            }
            j += 1;
        }
        pass += 1;
    }
    
    indices
}
// </vc-code>


}
fn main() {}