use vstd::prelude::*;

verus! {

// <vc-helpers>
fn rec_build(inputs: Map<nat, bool>, keys: Seq<nat>, f: spec_fn(nat) -> nat, i: nat) -> Map<nat, bool>
    requires keys == inputs.keys()
    requires i <= keys.len()
    requires forall|n1: nat, n2: nat| #[trigger] f(n1) != #[trigger] f(n2) ==> n1 != n2,
    decreases keys.len() - i
    ensures forall|k: nat| inputs.contains_key(k) <==> result.contains_key(f(k));
    ensures forall|k: nat| inputs.contains_key(k) ==> result[f(k)] == inputs[k];
{
    if i >= keys.len() {
        Map::new()
    } else {
        let k: nat = keys@[i];
        let rest: Map<nat, bool> = rec_build(inputs, keys, f, i + 1);
        rest.insert(f(k), inputs[k])
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
    rec_build(inputs, inputs.keys(), f, 0)
}
// </vc-code>

fn main() {}

}