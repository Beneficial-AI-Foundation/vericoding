use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PlusOne(x: int) -> (y: int)
    requires
        x >= 0,
    ensures
        y > 0,
{
    let result = x + 1;
    assert(result > 0);
    result
}

}