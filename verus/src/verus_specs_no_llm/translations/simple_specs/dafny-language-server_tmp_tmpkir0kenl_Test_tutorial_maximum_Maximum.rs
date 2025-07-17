// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Maximum(values: Seq<int>) -> max: int
    requires
        values != []
    ensures
        max in values,
        forall i  0 <= i < .len()values| :: values.index(i) <= max
;

proof fn lemma_Maximum(values: Seq<int>) -> (max: int)
    requires
        values != []
    ensures
        max in values,
        forall i  0 <= i < .len()values| :: values.index(i) <= max
{
    0
}

}