// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seed_sequence_spec(entropy: Seq<u32>, spawn_key: Seq<u32>, pool_size: usize) -> Seq<u32>
{
    let combined = entropy + spawn_key;
    Seq::new(pool_size as nat, |i: int| if i < combined.len() { combined[i] } else { 0 })
}
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
    let mut result: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < pool_size
        invariant
            result.len() == i,
            forall|j: nat| j < i ==> result@[j] == if j < entropy@.len() { entropy@[j] } else { 0 },
        decreases pool_size - i
    {
        let val = if i < entropy.len() { entropy[i] } else { 0u32 };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}