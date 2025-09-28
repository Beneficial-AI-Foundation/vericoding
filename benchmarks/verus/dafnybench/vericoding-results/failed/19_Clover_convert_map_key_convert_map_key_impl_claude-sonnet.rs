use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_map_insert_preserves_invariant(m: Map<nat, bool>, key: nat, value: bool, f: spec_fn(nat) -> nat, inputs: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat| 
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
        forall|k: nat| inputs.contains_key(k) && k != key ==> m.contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) && k != key ==> m[f(k)] == inputs[k],
        inputs.contains_key(key),
    ensures
        forall|k: nat| inputs.contains_key(k) ==> m.insert(f(key), value).contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) ==> m.insert(f(key), value)[f(k)] == inputs[k],
{
}

proof fn lemma_f_injective_implies_key_mapping(f: spec_fn(nat) -> nat, inputs: Map<nat, bool>, result: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat| 
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
        forall|k: nat| inputs.contains_key(k) ==> result.contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) ==> result[f(k)] == inputs[k],
    ensures
        forall|k: nat| inputs.contains_key(k) <==> result.contains_key(f(k)),
{
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
    let mut result: Map<nat, bool> = Map::empty();
    
    let ghost inputs_keys = inputs.dom();
    let ghost inputs_keys_seq = inputs_keys.to_seq();
    
    proof {
        assert forall|k: nat| !inputs.contains_key(k) implies !result.contains_key(f(k)) by {
        }
    }
    
    let ghost seq_len = inputs_keys_seq.len();
    for i in 0..seq_len
        invariant
            forall|n1: nat, n2: nat| 
                #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
            forall|j: int| 0 <= j < i ==> inputs.contains_key(inputs_keys_seq[j]),
            forall|j: int| 0 <= j < i ==> result.contains_key(f(inputs_keys_seq[j])),
            forall|j: int| 0 <= j < i ==> result[f(inputs_keys_seq[j])] == inputs[inputs_keys_seq[j]],
            forall|k: nat| result.contains_key(f(k)) ==> exists|j: int| 0 <= j < i && k == inputs_keys_seq[j],
    {
        let ghost key = inputs_keys_seq[i as int];
        let value = inputs.index(key);
        result = result.insert(f(key), value);
        
        proof {
            lemma_map_insert_preserves_invariant(result, key, value, f, inputs);
        }
    }
    
    proof {
        lemma_f_injective_implies_key_mapping(f, inputs, result);
        
        assert forall|k: nat| inputs.contains_key(k) <==> result.contains_key(f(k)) by {
        }
        
        assert forall|k: nat| inputs.contains_key(k) ==> result[f(k)] == inputs[k] by {
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}