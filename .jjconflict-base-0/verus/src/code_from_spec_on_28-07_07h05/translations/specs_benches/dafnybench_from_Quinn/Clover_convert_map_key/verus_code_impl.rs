use vstd::prelude::*;

verus! {
    // This is the main function that corresponds to the Dafny method
    spec fn convert_map_key(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> Map<nat, bool>
        recommends forall|n1: nat, n2: nat| n1 != n2 ==> #[trigger] f(n1) != #[trigger] f(n2)
    {
        // Equivalent to Dafny's: map k | k in inputs :: f(k) := inputs[k]
        Map::new(
            |k: nat| exists|orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == k,
            |k: nat| {
                let orig_k = choose|orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == k;
                inputs.index(orig_k)
            }
        )
    }
    
    // Proof that the function satisfies the original Dafny postconditions
    proof fn convert_map_key_correct(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat)
        requires forall|n1: nat, n2: nat| n1 != n2 ==> #[trigger] f(n1) != #[trigger] f(n2),
        ensures 
            ({
                let r = convert_map_key(inputs, f);
                // Corresponds to: forall k :: k in inputs <==> f(k) in r
                (forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k))) &&
                // Corresponds to: forall k :: k in inputs ==> r[f(k)] == inputs[k]
                (forall|k: nat| inputs.contains_key(k) ==> r.index(f(k)) == inputs.index(k))
            })
    {
        let r = convert_map_key(inputs, f);
        
        // Proof is automatically handled by the SMT solver given the definition
    }
}

fn main() {}