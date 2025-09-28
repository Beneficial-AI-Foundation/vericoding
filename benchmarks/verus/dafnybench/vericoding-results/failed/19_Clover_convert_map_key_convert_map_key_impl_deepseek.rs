use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_map_equality<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k: K| m1.contains_key(k) <==> m2.contains_key(k),
        forall|k: K| m1.contains_key(k) ==> m1[k] == m2[k],
    ensures
        m1 = m2,
{
}

proof fn lemma_f_injective(f: spec_fn(nat) -> nat)
    requires
        forall|n1: nat, n2: nat| #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    ensures
        forall|n1: nat, n2: nat| n1 != n2 ==> #[trigger] f(n1) != #[trigger] f(n2),
{
}

proof fn lemma_map_keys_containment<K, V>(m: Map<K, V>)
    ensures
        forall|k: K| m.contains_key(k) ==> m.dom().contains(k),
{
}

spec fn map_dom_contains_key<K, V>(m: Map<K, V>, k: K) -> bool
    recommends m.contains_key(k)
{
    m.dom().contains(k)
}

proof fn lemma_set_to_vec_construction(s: Set<nat>) -> (v: Vec<nat>)
    ensures
        v@.len() == s.len(),
        forall|j: int| 0 <= j < s.len() ==> s.contains(v@[j]),
        forall|k: nat| s.contains(k) ==> v@.contains(k),
{
    let mut vec = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            vec@.len() == i,
            forall|j: int| 0 <= j < i ==> s.contains(vec@[j]),
            forall|k: nat| s.contains(k) ==> vec@.contains(k),
    {
        let elem = s.choose();
        vec.push(elem);
        i = i + 1;
    }
    vec
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
    let mut result = Map::<nat, bool>::empty();
    
    proof {
        lemma_f_injective(f);
    }
    
    let keys: Set<nat> = inputs.dom();
    let keys_vec: Vec<nat> = proof {
        lemma_set_to_vec_construction(keys)
    };
    
    let mut i: int = 0;
    
    while i < keys.len()
        invariant
            0 <= i <= keys.len(),
            forall|k: nat| #[trigger] result.contains_key(f(k)) == keys.contains(k),
            forall|k: nat| keys.contains(k) ==> result[f(k)] == inputs[k],
    {
        let key = keys_vec[i as nat];
        let new_key = f(key);
        let value = inputs[key];
        
        result = result.insert(new_key, value);
        
        proof {
            assert forall|k: nat| keys.contains(k) implies result.contains_key(f(k)) by {
                if k == key {
                    assert(result.contains_key(f(k)));
                } else {
                    lemma_f_injective(f);
                    assert(f(k) != f(key));
                    assert(keys.contains(k));
                    assert(result.contains_key(f(k)));
                }
            };
            
            assert forall|k: nat| keys.contains(k) implies result[f(k)] == inputs[k] by {
                if k == key {
                    assert(result[f(k)] == inputs[k]);
                } else {
                    lemma_f_injective(f);
                    assert(f(k) != f(key));
                    assert(keys.contains(k));
                    assert(result[f(k)] == inputs[k]);
                }
            };
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}