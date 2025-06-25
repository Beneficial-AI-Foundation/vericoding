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

fn main(x: int) -> (j: int, i: int)
    requires
        x > 0
    ensures
        j == 2 * x
{
    return (0, 0);
}

}