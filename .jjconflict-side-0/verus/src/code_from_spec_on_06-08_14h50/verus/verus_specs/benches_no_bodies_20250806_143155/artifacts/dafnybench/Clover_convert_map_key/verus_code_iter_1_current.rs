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
        
        // Prove the first postcondition: forall k :: k in inputs <==> f(k) in r
        assert forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)) by {
            // Forward direction: if k in inputs, then f(k) in r
            if inputs.contains_key(k) {
                // By definition of r, f(k) is in r because there exists orig_k (namely k) 
                // such that inputs.contains_key(orig_k) && f(orig_k) == f(k)
                assert(exists|orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == f(k));
                assert(r.contains_key(f(k)));
            }
            
            // Backward direction: if f(k) in r, then k in inputs
            if r.contains_key(f(k)) {
                // By definition of r, there exists some orig_k such that 
                // inputs.contains_key(orig_k) && f(orig_k) == f(k)
                let orig_k = choose|orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == f(k);
                // Since f is injective and f(orig_k) == f(k), we have orig_k == k
                assert(f(orig_k) == f(k));
                if orig_k != k {
                    assert(f(orig_k) != f(k)); // contradiction with injectivity
                }
                assert(orig_k == k);
                assert(inputs.contains_key(k));
            }
        };
        
        // Prove the second postcondition: forall k :: k in inputs ==> r[f(k)] == inputs[k]
        assert forall|k: nat| inputs.contains_key(k) ==> r.index(f(k)) == inputs.index(k) by {
            if inputs.contains_key(k) {
                // By definition of r.index, r[f(k)] is computed as:
                // inputs[choose |orig_k| inputs.contains_key(orig_k) && f(orig_k) == f(k)]
                let chosen_k = choose|orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == f(k);
                // Since f is injective and we know inputs.contains_key(k) && f(k) == f(k),
                // the choose will select k (or any key that maps to f(k), but by injectivity, only k does)
                assert(inputs.contains_key(chosen_k) && f(chosen_k) == f(k));
                if chosen_k != k {
                    assert(f(chosen_k) != f(k)); // contradiction with injectivity
                }
                assert(chosen_k == k);
                assert(r.index(f(k)) == inputs.index(chosen_k));
                assert(r.index(f(k)) == inputs.index(k));
            }
        };
    }
}

fn main() {}