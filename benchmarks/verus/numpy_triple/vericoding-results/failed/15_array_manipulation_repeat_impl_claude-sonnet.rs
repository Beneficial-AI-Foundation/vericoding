// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in inner_loop_invariant_helper ensures clause */
spec fn valid_index_relation(i: int, repeats: int, a_len: int) -> bool {
    let k = i / repeats;
    0 <= k < a_len
}

proof fn index_division_lemma(i: int, repeats: int, a_len: int)
    requires repeats > 0, 0 <= i < a_len * repeats
    ensures valid_index_relation(i, repeats, a_len)
{
    let k = i / repeats;
    assert(0 <= i < a_len * repeats);
    assert(k >= 0);
    assert(k < a_len);
}

proof fn inner_loop_invariant_helper(rep: int, j: int, repeats: int, a_len: int)
    requires repeats > 0, 0 <= rep < repeats, 0 <= j < a_len
    ensures ({
        let current_len = a_len * rep + j;
        let new_len = current_len + 1;
        let k = current_len / repeats;
        k == rep && current_len % repeats == j
    })
{
    let current_len = a_len * rep + j;
    assert(current_len / repeats == rep);
    assert(current_len % repeats == j);
}
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting j to int */
    let mut result = Vec::new();
    let mut rep = 0;
    
    while rep < repeats
        invariant
            0 <= rep <= repeats,
            result.len() == a.len() * rep,
            forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
                let k = i / (repeats as int);
                0 <= k < a.len() && result[i] == a[k]
            }
        decreases repeats - rep
    {
        let mut j = 0;
        while j < a.len()
            invariant
                0 <= rep < repeats,
                0 <= j <= a.len(),
                result.len() == a.len() * rep + j,
                forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
                    if i < a.len() * rep {
                        let k = i / (repeats as int);
                        0 <= k < a.len() && result[i] == a[k]
                    } else {
                        let offset = i - a.len() * rep;
                        0 <= offset < j && result[i] == a[offset]
                    }
                }
            decreases a.len() - j
        {
            result.push(a[j]);
            
            proof {
                let current_idx = a.len() * rep + j;
                assert(current_idx < result.len());
                assert(result[current_idx] == a[j as int]);
                
                // Prove the postcondition holds for the new element
                let k = current_idx / (repeats as int);
                assert(k == rep);
                assert(0 <= k < a.len());
                assert(result[current_idx] == a[k]);
            }
            
            j += 1;
        }
        rep += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}