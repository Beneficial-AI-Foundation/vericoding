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
    
    assert forall|k: nat| inputs.dom().contains(k) 
        implies result_map.dom().contains(f(k)) by {
        assert(exists|k2: nat| inputs.dom().contains(k2) && f(k2) == f(k)) by {
            assert(inputs.dom().contains(k) && f(k) == f(k));
        }
    };
    
    assert forall|fk: nat| result_map.dom().contains(fk) 
        implies exists|k: nat| inputs.dom().contains(k) && f(k) == fk by {
        // This follows directly from the domain definition
    };
    
    assert forall|k: nat| inputs.dom().contains(k) 
        implies result_map[f(k)] == inputs[k] by {
        let fk = f(k);
        assert(result_map.dom().contains(fk));
        let chosen_k = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == fk;
        // By injectivity of f and the fact that f(k) == fk, we have chosen_k == k
        assert(f(chosen_k) == f(k));
        assert(chosen_k == k) by {
            // This follows from injectivity: if f(chosen_k) == f(k), then chosen_k == k
        };
        assert(result_map[fk] == inputs[chosen_k]);
        assert(result_map[fk] == inputs[k]);
    };
    
    result_map
}

}