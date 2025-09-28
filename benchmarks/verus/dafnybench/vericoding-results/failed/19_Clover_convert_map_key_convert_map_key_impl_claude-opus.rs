use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to recursively build the transformed map
spec fn convert_map_key_rec(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat, remaining: Set<nat>) -> Map<nat, bool>
    decreases remaining.len(),
{
    if remaining.len() == 0 {
        Map::empty()
    } else {
        let k = remaining.choose();
        let rest = convert_map_key_rec(inputs, f, remaining.remove(k));
        if inputs.contains_key(k) {
            rest.insert(f(k), inputs[k])
        } else {
            rest
        }
    }
}

// Prove properties about the recursive helper
proof fn convert_map_key_rec_ensures(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat, remaining: Set<nat>)
    requires
        forall|n1: nat, n2: nat| 
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
        forall|k: nat| remaining.contains(k) ==> inputs.contains_key(k),
    ensures
        forall|k: nat| 
            remaining.contains(k) ==> 
            convert_map_key_rec(inputs, f, remaining).contains_key(f(k)),
        forall|k: nat| 
            remaining.contains(k) ==> 
            convert_map_key_rec(inputs, f, remaining)[f(k)] == inputs[k],
        forall|fk: nat|
            convert_map_key_rec(inputs, f, remaining).contains_key(fk) ==>
            exists|k: nat| remaining.contains(k) && f(k) == fk && inputs.contains_key(k),
    decreases remaining.len(),
{
    if remaining.len() == 0 {
    } else {
        let k = remaining.choose();
        let rest_set = remaining.remove(k);
        convert_map_key_rec_ensures(inputs, f, rest_set);
        let rest = convert_map_key_rec(inputs, f, rest_set);
        let result = if inputs.contains_key(k) {
            rest.insert(f(k), inputs[k])
        } else {
            rest
        };
        
        assert forall|k2: nat| remaining.contains(k2) implies result.contains_key(f(k2)) by {
            if k2 == k {
                assert(inputs.contains_key(k));
                assert(result.contains_key(f(k)));
            } else {
                assert(rest_set.contains(k2));
                assert(rest.contains_key(f(k2)));
                if f(k2) != f(k) {
                    assert(result.contains_key(f(k2)));
                } else {
                    // f is injective, so this is impossible
                    assert(k2 != k);
                    assert(f(k2) != f(k));
                    assert(false);
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn convert_map_key(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> (r: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat| 
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    ensures
        forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) ==> r[f(k)] == inputs[k],
// </vc-spec>
// <vc-code>
{
    let result = convert_map_key_rec(inputs, f, inputs.dom());
    
    proof {
        convert_map_key_rec_ensures(inputs, f, inputs.dom());
        
        assert forall|k: nat| inputs.contains_key(k) implies result.contains_key(f(k)) by {
            assert(inputs.dom().contains(k));
        }
        
        assert forall|k: nat| result.contains_key(f(k)) implies inputs.contains_key(k) by {
            let k_witness = choose|k2: nat| inputs.dom().contains(k2) && f(k2) == f(k) && inputs.contains_key(k2);
            assert(inputs.contains_key(k_witness));
            assert(f(k_witness) == f(k));
            if k != k_witness {
                assert(f(k) != f(k_witness));
                assert(false);
            }
            assert(k == k_witness);
        }
        
        assert forall|k: nat| inputs.contains_key(k) implies result[f(k)] == inputs[k] by {
            assert(inputs.dom().contains(k));
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}