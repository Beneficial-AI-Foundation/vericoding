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
    
    // Prove first direction of the biconditional: inputs.dom().contains(k) ==> result_map.dom().contains(f(k))
    assert forall|k: nat| inputs.dom().contains(k) 
        implies result_map.dom().contains(f(k)) by {
        let fk = f(k);
        assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == fk) by {
            assert(inputs.dom().contains(k) && f(k) == fk);
        }
    };
    
    // Prove second direction: result_map.dom().contains(f(k)) ==> inputs.dom().contains(k) when inputs.dom().contains(k)
    assert forall|k: nat| inputs.dom().contains(k) <==> result_map.dom().contains(f(k)) by {
        if inputs.dom().contains(k) {
            // Forward direction already proven above
            assert(result_map.dom().contains(f(k)));
        }
        if result_map.dom().contains(f(k)) && inputs.dom().contains(k) {
            // This is trivially true when both conditions hold
        }
    };
    
    // Prove the value correspondence
    assert forall|k: nat| inputs.dom().contains(k) 
        implies result_map[f(k)] == inputs[k] by {
        let fk = f(k);
        assert(result_map.dom().contains(fk));
        
        // The chosen key must satisfy the condition
        let chosen_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == fk;
        assert(inputs.dom().contains(chosen_k) && f(chosen_k) == fk);
        
        // By injectivity: since f(chosen_k) == fk == f(k) and both chosen_k and k are in inputs.dom(),
        // we must have chosen_k == k
        assert(f(chosen_k) == f(k));
        if chosen_k != k {
            assert(false) by {
                // This contradicts injectivity
                assert(inputs.dom().contains(chosen_k));
                assert(inputs.dom().contains(k));
                assert(f(chosen_k) == f(k));
                assert(chosen_k != k);
                // The precondition says: forall n1, n2. n1 != n2 ==> f(n1) != f(n2)
                // Contrapositive: f(n1) == f(n2) ==> n1 == n2
                // So f(chosen_k) == f(k) ==> chosen_k == k, contradiction
            }
        }
        assert(chosen_k == k);
        assert(result_map[fk] == inputs[chosen_k]);
        assert(result_map[fk] == inputs[k]);
    };
    
    result_map
}

}