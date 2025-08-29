use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_all_equal_via_first(seq: &Vec<Vec<i32>>, first_len: usize)
    requires
        seq.len() > 0,
        forall|k: int| (0 <= k < seq.len()) ==> seq[k as int].len() == first_len,
    ensures
        forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> seq[i].len() == seq[j].len(),
{
    assert(forall|i: int, j: int| (0 <= i < seq.len() && 0 <= j < seq.len()) ==> {
        seq[i].len() == first_len && seq[j].len() == first_len
    });
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    if seq.len() == 1 {
        return true;
    }
    
    let first_len = seq[0].len();
    
    for i in 1..seq.len()
        invariant
            forall|k: int| (0 <= k < i) ==> seq[k as int].len() == first_len,
    {
        if seq[i].len() != first_len {
            /* code modified by LLM (iteration 2): added proof that postcondition holds when returning false */
            proof {
                assert(seq[i as int].len() != first_len);
                assert(seq[0].len() == first_len);
                assert(!(seq[i as int].len() == seq[0].len()));
                assert(!(forall|x: int, y: int| (0 <= x < seq.len() && 0 <= y < seq.len()) ==> seq[x].len() == seq[y].len()));
            }
            return false;
        }
    }
    
    /* code modified by LLM (iteration 2): added proof that postcondition holds when returning true */
    proof {
        assert(forall|k: int| (0 <= k < seq.len()) ==> seq[k as int].len() == first_len);
        lemma_all_equal_via_first(seq, first_len);
    }
    
    true
}
// </vc-code>

} // verus!

fn main() {}