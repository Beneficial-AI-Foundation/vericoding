// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountTrue(a: Vec<bool>) -> (result: int)
    requires
        a != null
    ensures
        result == countTo(a, a.len())
{
    return 0;
}

}