use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M() -> (r: int)
    ensures
        r == 29
{
    return 29;
}

}