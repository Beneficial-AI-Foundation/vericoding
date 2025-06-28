// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Quotient(a: int, b: int) -> (result: int)
    requires
        b != 0
    ensures
        result == a / b
{
    return 0;
}

}