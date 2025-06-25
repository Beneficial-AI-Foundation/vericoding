use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn add(x: int, y: int) -> (r: int)
    ensures r == x+y;
{
    return 0;
}

}

