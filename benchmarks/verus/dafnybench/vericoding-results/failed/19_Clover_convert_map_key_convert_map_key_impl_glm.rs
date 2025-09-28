use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_map_insert_invariant<K, V>(map: Map<K, V>, key: K, value: V)
    ensures
        forall|k: K| k != key ==> (map.insert(key, value)).contains_key(k) <==> map.contains_key(k),
        forall|k: K| k != key ==> (map.insert(key, value)).contains_key(k) ==> (map.insert(key, value))[k] == map[k],
{
    assert(forall|k: K| k != key ==> #[trigger] (map.insert(key, value)).contains_key(k) <==> map.contains_key(k));
    assert(forall|k: K| k != key ==> (map.insert(key, value)).contains_key(k) ==> (map.insert(key, value))[k] == map[k]);
}

proof fn lemma_map_insert_same_key<K, V>(map: Map<K, V>, key: K, value: V)
    ensures
        (map.insert(key, value)).contains_key(key),
        (map.insert(key, value))[key] == value,
{
    assert((map.insert(key, value)).contains_key(key));
    assert((map.insert(key, value))[key] == value);
}

proof fn lemma_set_insert<T>(set: Set<T>, elem: T)
    ensures
        forall|t: T| #[trigger] set.insert(elem).contains(t) <==> (set.contains(t) || t == elem),
{
    assert(forall|t: T| set.insert(elem).contains(t) <==> (set.contains(t) || t == elem));
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
    let mut r = Map::empty();
    let inputs_seq = inputs.dom().to_seq();
    let n = inputs_seq.len() as int;
    ghost let mut processed = Set::<nat>::empty();

    for i in 0..n
        invariant
            0 <= i <= n,
            processed.len() == i,
            forall|k: nat| 
                inputs.contains_key(k) ==> 
                    (r.contains_key(f(k)) <==> processed.contains(k)),
            forall|k: nat| 
                inputs.contains_key(k) && processed.contains(k) 
                    ==> r[f(k)] == inputs[k],
            forall|k: nat| 
                r.contains_key(k) <==> exists|n: nat| processed.contains(n) && f(n) == k,
    {
        let current_key = inputs_seq[i];
        let old_r = r;
        r = r.insert(f(current_key), inputs[current_key]);
        ghost let old_processed = processed;
        processed = processed.insert(current_key);
        
        lemma_map_insert_invariant(old_r, f(current_key), inputs[current_key]);
        lemma_map_insert_same_key(old_r, f(current_key), inputs[current_key]);
        lemma_set_insert(old_processed, current_key);

        assert forall|k: nat| 
            inputs.contains_key(k) ==> 
                (r.contains_key(f(k)) <==> processed.contains(k))
        by {
            if k == current_key {
                assert(r.contains_key(f(k)) && processed.contains(k));
            } else {
                lemma_map_insert_invariant(old_r, f(current_key), inputs[current_key]);
                assert(r.contains_key(f(k)) <==> old_r.contains_key(f(k)));
                assert(processed.contains(k) <==> old_processed.contains(k));
                assert(old_r.contains_key(f(k)) <==> old_processed.contains(k));
            }
        }

        assert forall|k: nat| 
            inputs.contains_key(k) && processed.contains(k) 
                ==> r[f(k)] == inputs[k]
        by {
            if k == current_key {
                assert(r[f(k)] == inputs[k]);
            } else {
                lemma_map_insert_invariant(old_r, f(current_key), inputs[current_key]);
                assert(r[f(k)] == old_r[f(k)]);
                assert(old_r[f(k)] == inputs[k]);
            }
        }

        assert forall|k: nat| 
            r.contains_key(k) <==> exists|n: nat| processed.contains(n) && f(n) == k
        by {
            if k == f(current_key) {
                assert(exists|n: nat| processed.contains(n) && f(n) == k);
            } else {
                lemma_map_insert_invariant(old_r, f(current_key), inputs[current_key]);
                assert(r.contains_key(k) <==> old_r.contains_key(k));
                assert(exists|n: nat| processed.contains(n) && f(n) == k <==> exists|n: nat| old_processed.contains(n) && f(n) == k);
            }
        }
    }
    
    r
}
// </vc-code>

fn main() {}

}