use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn two(x: int) -> (y: int)
    ensures
        y == x + 1
{
    x + 1
}

}