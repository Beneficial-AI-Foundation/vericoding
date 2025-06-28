use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: int, b: int) -> (z: int)
    requires
        true
    ensures
        z >= a || z >= b
{
    if a >= b {
        a
    } else {
        b
    }
}

}