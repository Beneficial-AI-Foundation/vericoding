use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    // pre-conditions-start
    requires
        seq.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let first_len = seq[0].len();
    let mut result = true;
    
    let mut i: usize = 1;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            result ==> (forall|k: int| 0 <= k < i ==> seq[k as usize].len() == first_len),
        decreases seq.len() - i,
    {
        if seq[i].len() != first_len {
            result = false;
        }
        i = i + 1;
    }
    
    // Ensure the postcondition holds by checking the entire sequence
    proof {
        if result {
            assert(forall|i: int, j: int| 
                (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i as usize].len() == seq[j as usize].len()) by {
                if 0 <= i < seq.len() && 0 <= j < seq.len() {
                    assert(seq[i as usize].len() == first_len);
                    assert(seq[j as usize].len() == first_len);
                }
            };
        } else {
            // If result is false, there must be at least two indices with different lengths
            let mut idx: usize = 1;
            let mut found_diff = false;
            let mut diff_i: int = 0;
            let mut diff_j: int = 0;
            while idx < seq.len()
                invariant
                    0 <= idx <= seq.len(),
                    !found_diff ==> (forall|k: int| 0 <= k < idx ==> seq[k as usize].len() == first_len),
                    found_diff ==> (0 <= diff_i < idx && 0 <= diff_j < idx && seq[diff_i as usize].len() != seq[diff_j as usize].len()),
                decreases seq.len() - idx,
            {
                if seq[idx].len() != first_len {
                    found_diff = true;
                    diff_i = 0;
                    diff_j = idx as int;
                    break;
                }
                idx = idx + 1;
            }
            if found_diff {
                assert(exists|i: int, j: int| 
                    0 <= i < seq.len() && 0 <= j < seq.len() && seq[i as usize].len() != seq[j as usize].len()) by {
                    assert(0 <= diff_i < seq.len());
                    assert(0 <= diff_j < seq.len());
                    assert(seq[diff_i as usize].len() != seq[diff_j as usize].len());
                };
            }
        }
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}