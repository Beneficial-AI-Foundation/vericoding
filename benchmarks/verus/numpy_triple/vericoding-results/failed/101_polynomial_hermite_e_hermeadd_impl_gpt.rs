// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate view indexing and int indexing for Vec<i32> */
proof fn lemma_vec_index_view_agree_i32(v: Vec<i32>, j: int)
    requires
        0 <= j < v.len()
    ensures
        v@[j] == v[j]
{
    assert(v@[j] == v[j]);
}

/* helper modified by LLM (iteration 5): executable helper linking usize exec indexing to int-spec view */
fn get_or_zero_i32(v: &Vec<i32>, i: usize) -> (res: i32)
    ensures
        res == (if (i as int) < v.len() { v@[(i as int)] } else { 0 })
{
    if i < v.len() { v[i] } else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push element-wise sums using wrapping_add; maintain invariant over result's view */
    let len1 = c1.len();
    let len2 = c2.len();
    let n = if len1 >= len2 { len1 } else { len2 };

    let mut result: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if 0 <= j && j < len1 { c1[j] } else { 0 };
                let coeff2 = if 0 <= j && j < len2 { c2[j] } else { 0 };
                #[trigger] result@[j] == coeff1 + coeff2
            }
        decreases n - i
    {
        let a = get_or_zero_i32(&c1, i);
        let b = get_or_zero_i32(&c2, i);

        let old_len_i: int = i as int; // equals result.len() as int by invariant
        // Push using wrapping_add to avoid overflow checks at runtime
        let sum = a.wrapping_add(b);
        result.push(sum);

        proof {
            // After push, the new element at index old_len_i equals 'sum'
            assert(result@[old_len_i] == sum);

            // Bridge get_or_zero_i32 results to spec-int indexing
            assert(a == (if old_len_i < len1 { c1@[(old_len_i)] } else { 0 }));
            assert(b == (if old_len_i < len2 { c2@[(old_len_i)] } else { 0 }));

            // When in-bounds, relate view and int-indexing for Vec
            if 0 <= old_len_i && old_len_i < len1 {
                lemma_vec_index_view_agree_i32(c1.clone(), old_len_i);
                assert(c1@[old_len_i] == c1[old_len_i]);
            }
            if 0 <= old_len_i && old_len_i < len2 {
                lemma_vec_index_view_agree_i32(c2.clone(), old_len_i);
                assert(c2@[old_len_i] == c2[old_len_i]);
            }

            // Show the invariant clause for j = i (the newly added index)
            let coeff1 = if 0 <= old_len_i && old_len_i < len1 { c1[old_len_i] } else { 0 };
            let coeff2 = if 0 <= old_len_i && old_len_i < len2 { c2[old_len_i] } else { 0 };

            // From helper postconditions and the above equalities:
            if old_len_i < len1 && old_len_i < len2 {
                // a == c1@[j] and b == c2@[j]
                // And c1@[j] == c1[j], c2@[j] == c2[j]
                assert(result@[old_len_i] == a.wrapping_add(b));
                assert(coeff1 == c1[old_len_i]);
                assert(coeff2 == c2[old_len_i]);
                // In spec, wrapping_add equals + for i32
                assert(a.wrapping_add(b) == a + b);
                assert(result@[old_len_i] == coeff1 + coeff2);
            } else if old_len_i < len1 {
                // b == 0
                assert(b == 0);
                assert(result@[old_len_i] == a.wrapping_add(0));
                assert(a.wrapping_add(0) == a + 0);
                if 0 <= old_len_i && old_len_i < len1 { assert(c1@[old_len_i] == c1[old_len_i]); }
                assert(coeff1 == c1[old_len_i]);
                assert(coeff2 == 0);
                assert(result@[old_len_i] == coeff1 + coeff2);
            } else if old_len_i < len2 {
                // a == 0
                assert(a == 0);
                assert(result@[old_len_i] == (0).wrapping_add(b));
                assert((0).wrapping_add(b) == 0 + b);
                if 0 <= old_len_i && old_len_i < len2 { assert(c2@[old_len_i] == c2[old_len_i]); }
                assert(coeff1 == 0);
                assert(coeff2 == c2[old_len_i]);
                assert(result@[old_len_i] == coeff1 + coeff2);
            } else {
                // both out of bounds: a == 0, b == 0
                assert(a == 0);
                assert(b == 0);
                assert(result@[old_len_i] == (0).wrapping_add(0));
                assert((0).wrapping_add(0) == 0 + 0);
                assert(coeff1 == 0);
                assert(coeff2 == 0);
                assert(result@[old_len_i] == coeff1 + coeff2);
            }
        }

        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}