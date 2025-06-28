// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    ensures
        more == x+y,
        less == x-y
{
    return (x + y, x - y);
}

}