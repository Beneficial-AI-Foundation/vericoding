use builtin::*;
use builtin_macros::*;

verus! {

fn main() -> (t1: int, t2: int, x: int, y: int)
    ensures
        y >= 1
{
    let result = (0, 0, 0, 1);
    assert(result.3 >= 1);
    result
}

}