// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed semicolon from empty proof block */
{
    let mut result_vec = Vec::new();
    verus_proof_sled!();
    let alloc: vstd::modes::Ghost<vstd::seq::Seq<T>> = Ghost(a.view());
    let old_a_len = a.len();

    if new_size == 0 {
        let res = Vec::new();
        return res;
    } else {
        if old_a_len == 0 {
            let mut i: usize = 0;
            while i < new_size
                invariant
                    i <= new_size,
                    result_vec.len() == i,
                    forall|j: int| 0 <= j < i ==> {
                        proof_assert!(alloc.0.len() == 0);
                        true
                    }
            {
                result_vec.push(arbitrary());
                i = i + 1;
            }
            proof {
                assert(result_vec.len() == new_size);
                assert(forall|i_v: int| 0 <= i_v < new_size ==> {
                    proof_assert!(alloc.0.len() == 0);
                    true
                });
            }
            return result_vec;
        }
    }

    let mut i: usize = 0;
    while i < new_size
        invariant
            i <= new_size,
            result_vec.len() == i,
            result_vec.len() <= new_size,
            old_a_len > 0,
            forall|j: int| 0 <= j < i ==> {
                if j < old_a_len {
                    result_vec@j == alloc.0@j
                } else {
                    result_vec@j == alloc.0@((j % old_a_len as int) as int)
                }
            }
    {
        if i < old_a_len {
            result_vec.push(a[i]);
        } else {
            let mod_idx = (i % old_a_len);
            result_vec.push(a[mod_idx]);
        }
        i = i + 1;
    }

    proof {
        assert(result_vec.len() == new_size);
        assert(forall|i_v: int| 0 <= i_v < new_size ==> {
            if i_v < old_a_len {
                result_vec@i_v == alloc.0@i_v
            } else {
                result_vec@i_v == alloc.0@((i_v % old_a_len as int) as int)
            }
        });
    }
    result_vec
}
// </vc-code>

}
fn main() {}