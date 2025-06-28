use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn F() -> (r: int)
    ensures
        r <= 0,
{
    let result = -1;
    assert(result <= 0);
    result
}

}