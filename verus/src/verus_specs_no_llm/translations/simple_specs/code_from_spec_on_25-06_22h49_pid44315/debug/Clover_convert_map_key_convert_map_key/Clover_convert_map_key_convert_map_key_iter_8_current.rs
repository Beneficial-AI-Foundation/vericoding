use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_injective<A, B>(f: spec_fn(A) -> B) -> bool {
    forall|x: A, y: A| x != y ==> f(x) != f(y)
}

fn convert_map_key<F>(inputs: Map<nat, bool>, f: F) -> (r: Map<nat, bool>)
    where F: Fn(nat) -> nat
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
            assert(inputs.dom().contains(k) && f(k) == fk);
            assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk);
            assert(result_map.dom().contains(fk));
        }
        
        // Reverse direction: if f(k) is in result_map.dom(), then k is in inputs.dom()
        if result_map.dom().contains(f(k)) {
            let fk = f(k);
            // By definition of result_map, f(k) in result_map.dom() means
            // there exists some k2 in inputs.dom() with f(k2) == f(k)
            assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk);
            let witness_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == fk;
            assert(inputs.dom().contains(witness_k) && f(witness_k) == f(k));
            
            // By injectivity: since f(witness_k) == f(k), we must have witness_k == k
            assert(f(witness_k) == f(k));
            if witness_k != k {
                // Use the injectivity precondition
                assert(f(witness_k) != f(k));
                assert(false);
            }
            assert(witness_k == k);
            assert(inputs.dom().contains(k));
        }
    };
    
    // Prove the value correspondence
    assert forall|k: nat| inputs.dom().contains(k) ==> result_map[f(k)] == inputs[k] by {
        if inputs.dom().contains(k) {
            let fk = f(k);
            // We know fk is in result_map.dom() from the previous proof
            assert(result_map.dom().contains(fk));
            let chosen_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == fk;
            assert(inputs.dom().contains(chosen_k) && f(chosen_k) == fk);
            
            // By injectivity: f(chosen_k) == f(k) implies chosen_k == k
            assert(f(chosen_k) == f(k));
            if chosen_k != k {
                // Use the injectivity precondition
                assert(f(chosen_k) != f(k));
                assert(false);
            }
            assert(chosen_k == k);
            assert(result_map[fk] == inputs[chosen_k]);
            assert(result_map[fk] == inputs[k]);
        }
    };
    
    result_map
}

}