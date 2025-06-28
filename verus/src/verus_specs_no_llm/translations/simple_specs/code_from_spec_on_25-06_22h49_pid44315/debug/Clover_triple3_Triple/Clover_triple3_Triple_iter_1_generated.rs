// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Triple(x: int) -> (r: int)
    ensures
        r == 3*x
{
    return 3 * x;
}

}