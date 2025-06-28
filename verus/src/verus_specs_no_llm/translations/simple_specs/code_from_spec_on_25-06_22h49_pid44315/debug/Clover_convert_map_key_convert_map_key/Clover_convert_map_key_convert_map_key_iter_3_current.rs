use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn convert_map_key(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> (r: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat| n1 != n2 ==> f(n1) != f(n2)
    ensures
        forall|k: nat| inputs.dom().contains(k) <==> r.dom().contains(f(k)),
        forall|k: nat| inputs.dom().contains(k) ==> r[f(k)] == inputs[k]
{
    let result_map = Map::new(
        |fk: nat| exists|k: nat| inputs.dom().contains(k) && f(k) == fk,
        |fk: nat| {
            let k = choose|k: nat| inputs.dom().contains(k) && f(k) == fk;
            inputs[k]
        }
    );
    
    // Prove the biconditional: inputs.dom().contains(k) <==> result_map.dom().contains(f(k))
    assert forall|k: nat| inputs.dom().contains(k) <==> result_map.dom().contains(f(k)) by {
        // Forward direction: if k is in inputs.dom(), then f(k) is in result_map.dom()
        if inputs.dom().contains(k) {
            let fk = f(k);
            // Show that there exists a key in inputs.dom() that maps to fk under f
            assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk) by {
                assert(inputs.dom().contains(k) && f(k) == fk);
            }
            assert(result_map.dom().contains(fk));
        }
        
        // Reverse direction: if f(k) is in result_map.dom(), then k is in inputs.dom()
        if result_map.dom().contains(f(k)) {
            let fk = f(k);
            // result_map.dom() contains fk means there exists some key that maps to fk
            assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk);
            
            // We need to show that k itself is in inputs.dom()
            // This is not automatically true from the above, so we need additional reasoning
            // However, the biconditional as stated in the postcondition may not hold
            // Let me reconsider the logic here
            
            // Actually, the reverse direction should be:
            // If there exists k such that inputs.dom().contains(k), then result_map.dom().contains(f(k))
            // The biconditional as written means: for any k, k is in inputs iff f(k) is in result
            // But this doesn't make sense if k is not in inputs originally
        }
    };
    
    // Let me fix the biconditional proof with correct logic
    assert forall|k: nat| inputs.dom().contains(k) ==> result_map.dom().contains(f(k)) by {
        let fk = f(k);
        assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk) by {
            assert(inputs.dom().contains(k) && f(k) == fk);
        }
    };
    
    assert forall|fk: nat| result_map.dom().contains(fk) ==> 
        (exists|k: nat| inputs.dom().contains(k) && f(k) == fk) by {
        // This follows from the definition of result_map.dom()
    };
    
    // The biconditional should hold due to injectivity
    assert forall|k: nat| inputs.dom().contains(k) <==> result_map.dom().contains(f(k)) by {
        if inputs.dom().contains(k) {
            // Forward direction proven above
        }
        if result_map.dom().contains(f(k)) {
            // By definition of result_map, f(k) in result_map.dom() means
            // there exists some k2 in inputs.dom() with f(k2) == f(k)
            // By injectivity, if f(k2) == f(k), then k2 == k
            // So k must be in inputs.dom()
            let witness_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == f(k);
            assert(inputs.dom().contains(witness_k) && f(witness_k) == f(k));
            assert(witness_k == k) by {
                // By injectivity (contrapositive): f(a) == f(b) ==> a == b
            }
            assert(inputs.dom().contains(k));
        }
    };
    
    // Prove the value correspondence
    assert forall|k: nat| inputs.dom().contains(k) ==> result_map[f(k)] == inputs[k] by {
        let fk = f(k);
        let chosen_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == fk;
        assert(inputs.dom().contains(chosen_k) && f(chosen_k) == fk);
        
        // By injectivity: f(chosen_k) == f(k) and both are valid implies chosen_k == k
        assert(chosen_k == k) by {
            // Contrapositive of injectivity
            if chosen_k != k {
                assert(f(chosen_k) != f(k)); // by injectivity precondition
                assert(false); // contradiction since f(chosen_k) == fk == f(k)
            }
        };
        assert(result_map[fk] == inputs[chosen_k]);
        assert(result_map[fk] == inputs[k]);
    };
    
    result_map
}

}