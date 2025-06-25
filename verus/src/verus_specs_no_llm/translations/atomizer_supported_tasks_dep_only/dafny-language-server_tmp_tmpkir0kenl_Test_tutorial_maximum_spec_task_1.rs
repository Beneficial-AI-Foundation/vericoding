// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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