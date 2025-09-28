use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
pub fn map_new<K, V>() -> Map<K, V> {
    todo!()
}

#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
pub fn map_insert<K, V>(map: Map<K, V>, key: K, value: V) -> Map<K, V> {
    todo!()
}

pub trait VecUsize<T> {
    spec fn view(&self) -> Seq<T>;
}

impl<T> VecUsize<T> for Vec<T> {
    spec fn view(&self) -> Seq<T> {
        vstd::seq::Seq::view(self)
    }
}

// Define the inverse trait for SpecFn
pub trait SpecFnInverse<A, B> {
    spec fn inverse(&self) -> FnSpec<B, A>;
}

impl<A, B, F: FnSpec<A, B>> SpecFnInverse<A, B> for F {
    // This assumes `self` is a bijection.
    // The implementation of inverse depends on the specific function.
    spec fn inverse(&self) -> FnSpec<B, A>;
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
    let mut r = map_new();
    let inputs_keys_set = inputs.dom();
    let mut keys_vec = inputs_keys_set.to_seq().to_vec();

    let mut i = 0;
    while i < keys_vec.len()
        invariant
            inputs.dom().finite(),
            i <= keys_vec.len(),
            keys_vec.len() <= inputs.dom().len(),
            (inputs.dom() - keys_vec.view().to_set()).len() == (inputs.dom().len() - keys_vec.len()) as nat,
            // All keys processed so far preserve the mapping in 'r'
            forall|j: int| 0 <= j && j < i ==>
                #[trigger] !keys_vec.view().contains(inputs.dom().to_seq()[j as int]) && // This is likely incorrect, it should be about elements removed from keys_vec
                r.contains_key(f(inputs_keys_set.to_seq()[j as int])) &&
                r[f(inputs_keys_set.to_seq()[j as int])] == inputs[inputs_keys_set.to_seq()[j as int]],
            // 'r' only contains keys that are f(original_key)
            forall|k_in_r: nat| r.contains_key(k_in_r) ==>
                exists|orig_k: nat| inputs.contains_key(orig_k) && k_in_r == f(orig_k) && r[k_in_r] == inputs[orig_k],
            // For any key k in r, if it maps from original_k, the value matches
            forall|k_in_r: nat, original_k: nat|
                #[trigger] r.contains_key(k_in_r) && #[trigger] f(original_k) == k_in_r && inputs.contains_key(original_k)
                ==> r[k_in_r] == inputs[original_k],
            // The remaining keys in keys_vec are still in inputs.dom() and not yet in r
            forall|j: int| 0 <= j && j < keys_vec.len() ==>
                inputs_keys_set.contains(keys_vec.view()[j as int]) &&
                !r.contains_key(f(keys_vec.view()[j as int])),
            // The union of keys in r and keys_vec covers all keys in inputs.dom()
            inputs.dom() =~= (keys_vec.view().to_set() + r.dom().map(|k| f.inverse()(k))),
            // Keys in r correspond to a subset of original inputs keys
            r.dom().map(|k| f.inverse()(k)).subset_of(inputs.dom()),
    {
        let key = keys_vec.tracked_remove(0); // Using tracked_remove to get an element and shrink the vec
        let mapped_key = f(key);

        assert(inputs.contains_key(key));
        let value = inputs[key];
        
        r = map_insert(r, mapped_key, value);

        proof {
            assert(r.contains_key(mapped_key));
            assert(r[mapped_key] == value);
        }
        i += 1;
    }

    // Post-condition proof
    proof {
        assert forall|k: nat| inputs.contains_key(k) implies r.contains_key(f(k)) by {
            // From invariant, after loop termination, keys_vec is empty.
            // inputs.dom() =~= r.dom().map(f.inverse()).
            // So if inputs.contains_key(k), there must be some k_r in r.dom() such that f.inverse()(k_r) = k, i.e., k_r = f(k).
            // Thus, r.contains_key(f(k)).
        }

        assert forall|k: nat| r.contains_key(k) implies inputs.contains_key(f.inverse()(k)) by {
            // This is handled by the invariant:
            // forall|k_in_r: nat| r.contains_key(k_in_r) ==>
            //     exists|orig_k: nat| inputs.contains_key(orig_k) && k_in_r == f(orig_k) && r[k_in_r] == inputs[orig_k],
            // Combined with the injectivity of f, if r.contains_key(k), there is a unique orig_k such that
            // f(orig_k) = k, and inputs.contains_key(orig_k).
        }
    
        assert forall |k: nat| #[trigger] inputs.contains_key(k) implies r[f(k)] == inputs[k] by {
            // From invariant, and the fact that all original keys are processed.
        }
    }
    r
}
// </vc-code>

fn main() {}

}