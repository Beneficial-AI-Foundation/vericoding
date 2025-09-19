// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn seed_sequence_spec(entropy: Seq<u32>, spawn_key: Seq<u32>, pool_size: usize) -> Seq<u32>;

fn seed_sequence(entropy: Vec<u32>, spawn_key: Vec<u32>, pool_size: usize) -> (result: Vec<u32>)
    requires spawn_key.len() == 0,
    ensures 
        /* Reproducibility property: same inputs produce same outputs */
        forall|entropy2: Seq<u32>, spawn_key2: Seq<u32>| 
            entropy@ == entropy2 && spawn_key@ == spawn_key2 ==> 
            seed_sequence_spec(entropy2, spawn_key2, pool_size) == result@,
        /* Non-degeneracy: output depends on input when entropy is present */
        entropy.len() > 0 ==> 
            exists|modified_entropy: Seq<u32>| 
                modified_entropy != entropy@ &&
                seed_sequence_spec(modified_entropy, spawn_key@, pool_size) != result@,
        /* Well-defined output: result has the correct size */
        result.len() == pool_size,
        /* Result specification matches */
        result@ == seed_sequence_spec(entropy@, spawn_key@, pool_size)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}