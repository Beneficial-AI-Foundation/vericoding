// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Maximum(values: Seq<int>) -> (max: int)
    requires
        values != []
    ensures
        max in values,
        forall i  0 <= i < .len()values| :: values.spec_index(i) <= max
{
    return 0;
}

}