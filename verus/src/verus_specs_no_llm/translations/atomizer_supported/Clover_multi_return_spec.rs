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

fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    ensures
        more == x+y,
        less == x-y
{
    return (0, 0);
}

}