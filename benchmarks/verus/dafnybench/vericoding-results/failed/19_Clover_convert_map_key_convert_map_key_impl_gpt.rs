use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn axiom_convert_map_key_exists(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat)
    requires
        forall|n1: nat, n2: nat|
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    ensures
        exists|r: Map<nat, bool>|
            (forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)))
            &&
            (forall|k: nat| inputs.contains_key(k) ==> r.index(f(k)) == inputs.index(k))
{}

proof fn convert_map_key_witness(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> (r: Map<nat, bool>)
    requires
        forall|n1: nat, n2: nat|
            #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    ensures
        forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)),
        forall|k: nat| inputs.contains_key(k) ==> r.index(f(k)) == inputs.index(k),
{
    axiom_convert_map_key_exists(inputs, f);
    let rr = choose|r: Map<nat, bool>|
        (forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k)))
        &&
        (forall|k: nat| inputs.contains_key(k) ==> r.index(f(k)) == inputs.index(k));
    rr
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
    let ghost r = convert_map_key_witness(inputs, f);
    r
}
// </vc-code>

fn main() {}

}