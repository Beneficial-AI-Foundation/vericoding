pub fn convert_map_key(inputs: Map<nat, bool>, f: spec_fn(nat) -> nat) -> (r: Map<nat, bool>)
    requires(
        forall|n1: nat, n2: nat| n1 != n2 ==> f(n1) != f(n2)
    )
    ensures(|r: Map<nat, bool>|
        forall|k: nat| inputs.contains_key(k) <==> r.contains_key(f(k))
    )
    ensures(|r: Map<nat, bool>|
        forall|k: nat| inputs.contains_key(k) ==> r[f(k)] == inputs[k]
    )
{
}