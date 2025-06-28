use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M(x: int) -> (seven: int)
    ensures
        seven == 7
{
    7
}

}