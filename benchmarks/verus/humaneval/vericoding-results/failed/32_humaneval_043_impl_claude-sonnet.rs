// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
spec fn is_mapped_seq_def(l: Seq<i8>, mapped: Seq<int>) -> bool {
    mapped.len() == l.len() &&
    forall|i: int| 0 <= i < l.len() ==> mapped[i] == l[i] as int
}

/* helper modified by LLM (iteration 5): add mapping property lemma */
proof fn lemma_mapping_property(l: Seq<i8>, i: int)
    requires 0 <= i < l.len()
    ensures l.map(|idx: int, x: i8| x as int)[i] == l[i] as int
{
    let mapped = l.map(|idx: int, x: i8| x as int);
    assert(mapped[i] == l[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplify invariants and fix mapping assertions */
    let ghost mapped_seq = l@.map(|i: int, x: i8| x as int);
    
    for i in 0..l.len()
        invariant
            forall|ii: int, jj: int| 0 <= ii < jj < i ==> mapped_seq[ii] + mapped_seq[jj] != 0
    {
        for j in (i + 1)..l.len()
            invariant
                i < l.len(),
                forall|ii: int, jj: int| 0 <= ii < jj < i ==> mapped_seq[ii] + mapped_seq[jj] != 0,
                forall|jjj: int| i < jjj < j ==> mapped_seq[i] + mapped_seq[jjj] != 0
        {
            proof {
                lemma_mapping_property(l@, i as int);
                lemma_mapping_property(l@, j as int);
            }
            if l[i] == -l[j] {
                proof {
                    assert(mapped_seq[i] == l@[i] as int);
                    assert(mapped_seq[j] == l@[j] as int);
                    assert(l@[i] as int + l@[j] as int == 0);
                    assert(mapped_seq[i] + mapped_seq[j] == 0);
                    assert(0 <= i < j < mapped_seq.len());
                    assert(has_pair_sum_to_zero(mapped_seq));
                }
                return true;
            }
        }
    }
    
    proof {
        if has_pair_sum_to_zero(mapped_seq) {
            let (i_wit, j_wit) = choose|i: int, j: int| 0 <= i < j < mapped_seq.len() && mapped_seq[i] + mapped_seq[j] == 0;
            assert(false);
        }
    }
    
    false
}
// </vc-code>


}

fn main() {}