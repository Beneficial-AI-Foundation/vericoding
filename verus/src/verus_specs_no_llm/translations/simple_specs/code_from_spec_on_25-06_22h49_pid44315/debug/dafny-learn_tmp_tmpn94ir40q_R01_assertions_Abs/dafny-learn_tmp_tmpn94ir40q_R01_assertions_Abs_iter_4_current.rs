use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Abs(x: int) -> int
{
    if x < 0 {
        -x
    } else {
        x
    }
}

}