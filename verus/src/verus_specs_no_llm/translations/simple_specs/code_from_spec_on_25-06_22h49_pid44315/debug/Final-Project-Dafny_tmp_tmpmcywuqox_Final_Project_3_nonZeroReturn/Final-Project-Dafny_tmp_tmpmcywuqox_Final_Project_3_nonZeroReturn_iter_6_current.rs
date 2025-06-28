use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn nonZeroReturn(x: int) -> (y: int)
    ensures
        y != 0
{
    let result = 1;
    assert(result != 0);
    result
}

}