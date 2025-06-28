use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Two(x: int) -> (y: int)
    ensures
        y == x + 1
{
    return x + 1;
}

}