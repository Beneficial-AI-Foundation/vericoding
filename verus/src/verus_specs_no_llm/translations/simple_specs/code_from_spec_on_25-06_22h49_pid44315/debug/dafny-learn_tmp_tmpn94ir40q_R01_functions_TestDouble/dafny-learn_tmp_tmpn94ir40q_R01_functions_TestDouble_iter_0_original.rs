// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TestDouble(val: int) -> (val2: int)
    ensures
        val2 == Double(val)
{
    return 0;
}

}