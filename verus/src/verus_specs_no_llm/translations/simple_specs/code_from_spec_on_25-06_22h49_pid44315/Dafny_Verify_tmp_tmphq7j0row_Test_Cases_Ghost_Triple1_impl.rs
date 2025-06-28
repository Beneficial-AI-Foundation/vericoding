use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple1(x: int) -> (r: int)
    ensures
        r == 3 * x
{
    3 * x
}

}