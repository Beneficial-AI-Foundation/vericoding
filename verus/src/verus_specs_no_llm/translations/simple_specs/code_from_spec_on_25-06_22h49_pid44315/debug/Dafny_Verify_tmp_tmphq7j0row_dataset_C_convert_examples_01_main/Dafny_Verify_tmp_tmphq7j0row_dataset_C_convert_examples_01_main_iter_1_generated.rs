use builtin::*;
use builtin_macros::*;

verus! {

fn main() -> (t1: int, t2: int, x: int, y: int)
    ensures
        y >= 1
{
    return (0, 0, 0, 1);
}

}