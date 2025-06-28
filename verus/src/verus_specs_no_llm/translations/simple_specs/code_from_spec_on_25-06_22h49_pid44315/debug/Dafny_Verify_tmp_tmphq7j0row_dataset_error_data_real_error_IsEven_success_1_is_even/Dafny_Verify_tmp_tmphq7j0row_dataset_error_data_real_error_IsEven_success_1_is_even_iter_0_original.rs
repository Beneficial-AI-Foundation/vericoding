// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn is_even(n: int) -> (r: bool)
    requires
        n >= 0
    ensures
        r <==> even(n)
{
    return false;
}

}