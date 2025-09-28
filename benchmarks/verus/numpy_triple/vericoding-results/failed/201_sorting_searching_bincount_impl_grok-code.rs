// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): fixed type mismatch in Seq.new closure by using nat literal */
    let total_bins = (max_val as usize) + 1;
    let mut counts: Vec<u8> = Vec::new();
    for _ in 0..total_bins {
        counts.push(0);
    }
    let ghost curr_counts: Seq<nat> = Seq::<nat>::new(total_bins as int, |i| 0nat);
    let mut pos = 0;
    while pos < x.len()
        invariant
            total_bins == (max_val as nat) + 1,
            curr_counts.len() == total_bins as int,
            forall |i: int| 0 <= i < total_bins as int ==> curr_counts[i] <= (pos as nat),
            pos <= x.len(),
            forall |val: int| 0 <= val < total_bins as int ==> 
                curr_counts[val] == count_occurrences(x@.take(pos as int).map_values(|v: u8| v as nat), val as nat),
        decreases x.len() - pos
    {
        let elem = x[pos];
        let elem_idx = elem as usize;
        proof {
            let elem_nat = elem as nat;
            curr_counts = curr_counts.update(elem_nat as int, curr_counts[elem_nat as int] + 1);
        }
        counts[elem_idx] += 1;
        pos += 1;
    }
    counts
}
// </vc-code>


}
fn main() {}