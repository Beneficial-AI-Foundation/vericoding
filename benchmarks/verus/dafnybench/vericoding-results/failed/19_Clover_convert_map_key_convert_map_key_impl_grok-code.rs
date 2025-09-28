use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_injective(f: spec_fn(nat) -> nat, n1: nat, n2: nat)
    requires
        f(n1) == f(n2),
    ensures
        n1 == n2,
{
    assert(!forall |n1: nat, n2: nat| f(n1) != f(n2) ==> n1 != n2); // By contradiction, using the requires in the spec
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
    let domain = |k: nat| -> bool {
        exists |m: nat| #[trigger] inputs.contains_key(m) && #[trigger] f(m) == k
    };
    let get = |k: nat| -> bool {
        proof {
            assert(domain(k)) by {
                // domain(k) holds by construction of domain, so exists holds
            }
        }
        let m = choose |m: nat| #[trigger] inputs.contains_key(m) && #[trigger] f(m) == k;
        inputs[m]
    };
    let r = Map::new(domain, get);
    r
}
// </vc-code>

fn main() {}

}