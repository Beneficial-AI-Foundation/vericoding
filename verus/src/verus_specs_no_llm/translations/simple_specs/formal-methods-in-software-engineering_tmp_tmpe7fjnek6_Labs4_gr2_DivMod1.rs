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

fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires
        b > 0 && a >= 0
    ensures
        a == b*q + r && 0 <= r < b
//decreases *
{
    return (0, 0);
}

}