use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn F() -> (r: int)
    ensures
        r <= 0
{
    0
}

}