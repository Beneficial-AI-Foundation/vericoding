// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper for sequence subsequence and fix `subsequence` call. The `subsequence` method is for `Seq<T>` not `Seq<u8>` directly, thus map the `u8` to `nat` outside of `subsequence`. */
spec fn get_subsequence_u8(s: Seq<u8>, start: nat, end: nat) -> Seq<nat>
    requires start <= end,
{
    s.subsequence(start as int, end as int).map(|k: int, v: u8| v as nat)
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
/* code modified by LLM (iteration 5): adjust subsequence call to `i as nat` to align with the helper function signature and fix `get_subsequence_u8` calls*/
{
    let mut counts: Vec<u8> = vec![0; (max_val as usize) + 1];
    let mut i = 0;
    while i < x.len()
        invariant
            counts.len() == (max_val as nat) + 1,
            0 <= i <= x.len(),
            forall|val: int| 0 <= val <= max_val as int ==> counts[val] as nat == count_occurrences(get_subsequence_u8(x@, 0, i as nat), val as nat),
        decreases x.len() - i
    {
        let val: usize = x[i] as usize;
        let current_count = counts[val];
        counts[val] = current_count.checked_add(1).unwrap_or(255);
        i = i + 1;
    }
    counts
}
// </vc-code>


}
fn main() {}