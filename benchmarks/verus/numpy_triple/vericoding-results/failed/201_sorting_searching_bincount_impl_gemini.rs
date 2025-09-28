// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using the correct vstd lemma 'lemma_filter_push'. */
#[verifier::spinoff_prover]
proof fn lemma_count_occurrences_snoc(s: Seq<nat>, v: nat, val: nat)
    ensures
        count_occurrences(s.push(v), val) == count_occurrences(s, val) + (if v == val { 1 } else { 0 }),
{
    vstd::seq_lib::lemma_filter_push(s, v, |u: nat| u == val);
}
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(x: Seq<nat>, val: nat) -> nat {
    x.filter(|v: nat| v == val).len()
}

fn numpy_bincount(x: Vec<u8>, max_val: u8) -> (result: Vec<u8>)
    requires 
        forall|i: int| 0 <= i < x.len() ==> x[i] as nat <= max_val as nat,
    ensures
        result.len() == max_val as nat + 1,
        forall|val: int| 0 <= val <= max_val as int ==> 
            result[val] as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), val as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Retained previous logic which should pass now that the helper is fixed. */
    let mut result = Vec::new_with_len(max_val as usize + 1, 0u8);
    let mut i: usize = 0;
    let ghost x_nat_view = x@.map(|_i: int, v: u8| v as nat);

    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == max_val as nat + 1,
            forall|val: int| 0 <= val <= max_val as int ==> 
                result@[val] as nat == count_occurrences(x_nat_view.subseq(0, i as nat), val as nat),
        decreases x.len() - i
    {
        let val = x[i];
        let val_idx = val as usize;

        let ghost result_old = result@;
        let ghost s_old = x_nat_view.subseq(0, i as nat);

        result.set(val_idx, result[val_idx] + 1);
        i = i + 1;
        
        let ghost s_new = x_nat_view.subseq(0, i as nat);
        
        assert forall|v_check: int| 0 <= v_check <= max_val as int implies
            result@[v_check] as nat == count_occurrences(s_new, v_check as nat)
        by {
            let val_nat = val as nat;
            let val_int = val as int;
            assert(s_new === s_old.push(val_nat));
            lemma_count_occurrences_snoc(s_old, val_nat, v_check as nat);
            if v_check == val_int {
                assert(result@[v_check] == result_old[v_check] + 1);
            } else {
                assert(result@[v_check] === result_old[v_check]);
            }
        }
    }
    result
}
// </vc-code>


}
fn main() {}