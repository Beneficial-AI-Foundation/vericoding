use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn simple(y: int) -> (result: int)
    requires
        y == 6
    ensures
        result == 7
{
    let x = y + 1;
    assert(x == 7);
    x
}

}