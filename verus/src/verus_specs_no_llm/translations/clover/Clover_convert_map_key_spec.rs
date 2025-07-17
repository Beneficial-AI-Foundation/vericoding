// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_convert_map_key(inputs: map<nat, bool>, f: nat->nat) -> r:map<nat, bool>
    requires
        forall |n1: nat, n2: nat| n1 != n2 ==> f(n1) != f(n2)
    ensures
        forall |k: int| k in inputs <==> f(k) in r,
        forall |k: int| k in inputs ==> r.index(f(k)) == inputs.index(k)
;

proof fn lemma_convert_map_key(inputs: map<nat, bool>, f: nat->nat) -> (r: map<nat, bool>)
    requires
        forall |n1: nat, n2: nat| n1 != n2 ==> f(n1) != f(n2)
    ensures
        forall |k: int| k in inputs <==> f(k) in r,
        forall |k: int| k in inputs ==> r.index(f(k)) == inputs.index(k)
{
    (0, 0)
}

}