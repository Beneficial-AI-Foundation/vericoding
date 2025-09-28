// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate function definition */
proof fn lemma_seed_sequence_reproducibility(entropy1: Seq<u32>, entropy2: Seq<u32>, spawn_key1: Seq<u32>, spawn_key2: Seq<u32>, pool_size: usize)
    requires entropy1 == entropy2 && spawn_key1 == spawn_key2,
    ensures seed_sequence_spec(entropy1, spawn_key1, pool_size) == seed_sequence_spec(entropy2, spawn_key2, pool_size)
{
    // Identity follows from the requirements
}

proof fn lemma_seed_sequence_non_degeneracy(entropy: Seq<u32>, spawn_key: Seq<u32>, pool_size: usize)
    requires entropy.len() > 0,
    ensures exists|modified_entropy: Seq<u32>| modified_entropy != entropy && seed_sequence_spec(modified_entropy, spawn_key, pool_size) != seed_sequence_spec(entropy, spawn_key, pool_size)
{
    // Create a modified entropy that differs in the first position
    let modified_entropy = entropy.update(0, entropy[0] ^ 0xFFFFFFFFu32);
    assert(modified_entropy != entropy);
    assert(seed_sequence_spec(modified_entropy, spawn_key, pool_size) != seed_sequence_spec(entropy, spawn_key, pool_size));
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
    /* code modified by LLM (iteration 5): removed duplicate function definition and fixed compilation */
    // Initialize result vector with zeros
    let mut result = Vec::new();
    
    // Fill the result vector with entropy values, cycling if needed
    let mut i = 0;
    while i < pool_size
        invariant
            0 <= i <= pool_size,
            result.len() == i,
        decreases pool_size - i
    {
        if entropy.len() == 0 {
            // If no entropy, use zeros
            result.push(0u32);
        } else {
            // Use entropy values, cycling if necessary
            let index = i % entropy.len();
            result.push(entropy[index]);
        }
        i += 1;
    }
    
    // Return the result
    result
}
// </vc-code>


}
fn main() {}