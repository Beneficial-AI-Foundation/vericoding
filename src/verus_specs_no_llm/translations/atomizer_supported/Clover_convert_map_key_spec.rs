// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn convert_map_key(inputs: map<nat, bool>, f: nat->nat) -> r: map<nat, bool>
    requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
    ensures forall|k: int| k in inputs <==> f(k) in r,
            forall|k: int| k in inputs ==> r[f(k)] == inputs[k]
{
}

}