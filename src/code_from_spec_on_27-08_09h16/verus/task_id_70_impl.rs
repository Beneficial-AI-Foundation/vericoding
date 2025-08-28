use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    // impl-start
    let first_len = seq[0].len();
    
    for i in 0..seq.len()
        invariant
            seq[0].len() == first_len,
            forall|k: int| 0 <= k < i ==> seq[k].len() == first_len,
    {
        if seq[i].len() != first_len {
            proof {
                assert(seq[i as int].len() != first_len);
                assert(seq[0].len() == first_len);
                assert(seq[i as int].len() != seq[0].len());
                assert(0 <= i < seq.len() && 0 <= 0 < seq.len());
                assert(exists|x: int, y: int| (0 <= x < seq.len() && 0 <= y < seq.len()) && seq[x].len() != seq[y].len()) by {
                    assert(seq[i as int].len() != seq[0].len());
                }
                assert(!(forall|x: int, y: int| (0 <= x < seq.len() && 0 <= y < seq.len()) ==> seq[x].len() == seq[y].len())) by {
                    assert(0 <= i < seq.len() && 0 <= 0 < seq.len());
                    assert(seq[i as int].len() != seq[0].len());
                }
            }
            return false;
        }
    }
    
    proof {
        assert(forall|k: int| 0 <= k < seq.len() ==> seq[k].len() == first_len);
        assert(forall|i: int, j: int| 
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> 
            (seq[i].len() == first_len && seq[j].len() == first_len));
        assert(forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len());
    }
    
    true
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}