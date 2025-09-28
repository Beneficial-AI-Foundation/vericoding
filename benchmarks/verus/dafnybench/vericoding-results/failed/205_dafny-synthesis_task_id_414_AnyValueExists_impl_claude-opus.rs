use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = 0;
    let mut found = false;
    
    while idx < seq1.len()
        invariant
            0 <= idx <= seq1.len(),
            found <==> (exists|j: int| 0 <= j < idx as int && seq2.contains(#[trigger] seq1[j])),
            !found ==> (forall|j: int| 0 <= j < idx as int ==> !seq2.contains(#[trigger] seq1[j])),
    {
        let current_val = seq1[idx as int];
        if seq2.contains(current_val) {
            found = true;
            proof {
                assert(seq2.contains(seq1[idx as int]));
                assert(0 <= idx as int && idx as int < seq1.len());
                assert(exists|j: int| 0 <= j < idx as int + 1 && seq2.contains(#[trigger] seq1[j]));
            }
            break;
        }
        idx = idx + 1;
    }
    
    proof {
        if found {
            assert(exists|i: int| 0 <= i < seq1.len() && seq2.contains(#[trigger] seq1[i]));
        } else {
            assert(idx as int == seq1.len());
            assert(forall|j: int| 0 <= j < seq1.len() ==> !seq2.contains(#[trigger] seq1[j]));
            assert(!(exists|i: int| 0 <= i < seq1.len() && seq2.contains(#[trigger] seq1[i])));
        }
    }
    
    found
}
// </vc-code>

fn main() {}

}