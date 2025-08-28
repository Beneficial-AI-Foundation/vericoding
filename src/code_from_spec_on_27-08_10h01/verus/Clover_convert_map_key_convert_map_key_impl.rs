use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn domain_fn(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> FnSpec<nat, bool> {
    |k: nat| exists |orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == k
}

spec fn value_fn(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> FnSpec<nat, bool> {
    |k: nat| {
        if exists |orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == k {
            let orig_k = choose |orig_k: nat| inputs.contains_key(orig_k) && f(orig_k) == k;
            inputs.index(orig_k)
        } else {
            arbitrary()
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn convert_map_key(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> (r: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat| 
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    ensures
        forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) ==> r[f(k)] == inputs[k],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: Map<nat, bool> = Map::empty();
    
    proof {
        assert forall |k1: nat, k2: nat| inputs.contains_key(k1) && inputs.contains_key(k2) && k1 != k2 
            implies f(k1) != f(k2) by {
        }
    }
    
    result = Map::new(
        domain_fn(inputs, f),
        value_fn(inputs, f)
    );
    
    result
}
// </vc-code>

fn main() {}

}